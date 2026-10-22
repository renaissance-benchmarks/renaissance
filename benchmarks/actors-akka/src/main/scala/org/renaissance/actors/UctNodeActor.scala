package org.renaissance.actors

import akka.actor.Actor
import akka.actor.ActorRef
import akka.actor.Props

import scala.collection.mutable

private[actors] object UctNodeActor {

  /**
   * Props of a node actor. They are built here rather than in the creating actor, so that
   * the closure that creates the node actor cannot capture the creating actor.
   */
  def props(id: NodeId, plan: ExpansionPlan): Props = Props(new UctNodeActor(id, plan))

  /**
   * A measurement taken by an interior node: the sum of the temperatures reported by its
   * children so far and the number of children yet to report.
   */
  private final case class Measurement(temperatureSum: Double, pendingReadingCount: Int) {

    def withReading(temperature: Double): Measurement =
      Measurement(temperatureSum + temperature, pendingReadingCount - 1)

    def isComplete: Boolean = pendingReadingCount == 0
  }
}

/**
 * A node of the UCT. The actor hierarchy follows the tree: the parent of the root node is
 * the [[UctCoordinatorActor]], the parent of every other node is another node. Nodes
 * exchange only actor-protocol messages and report completion of each phase upward
 * to their parent.
 */
private[actors] final class UctNodeActor(id: NodeId, plan: ExpansionPlan) extends Actor {

  // Tree structure, populated during the build phase, with the checksum of the subtree
  // and the leaf farthest from each child, as reported by the child.
  private val children: mutable.Buffer[ActorRef] = mutable.Buffer.empty
  private var subtreeChecksum: TreeChecksum = TreeChecksum.of(id)
  private val childFarthestLeaves = mutable.Map[ActorRef, LeafDistance]()

  // Children on urgent paths, populated during the urgent path selection.
  private val urgentChildren = mutable.Set[ActorRef]()

  // Offers collected in the current round of the urgent path selection, with the child
  // through which each offered leaf is reached.
  private val urgentPathOffers = mutable.Buffer[LeafDistance]()
  private val urgentPathOfferChildren = mutable.Map[NodeId, ActorRef]()
  private var urgentPathOfferCountMax: Int = 0

  // Pending-response counter, reused across the build, selection, and teardown phases.
  private var pendingResponseCount: Int = 0

  // Temperature state
  private var temperature: Option[Double] = None

  // Measurements still waiting for readings from the children.
  private val pendingMeasurements = mutable.Map[MeasurementId, UctNodeActor.Measurement]()

  override def receive: Receive = {
    // --- tree construction --------------------------------------------------

    case CreateSubtreeMessage =>
      handleCreateSubtree()

    case m: SubtreeCreatedMessage =>
      handleSubtreeCreated(sender(), m.checksum, m.farthestLeaf)

    // --- urgent path selection ----------------------------------------------

    case m: CollectUrgentPathOffersMessage =>
      handleCollectUrgentPathOffers(m.branchDistance, m.leafDistanceMin, m.offerCountMax)

    case m: UrgentPathOffersMessage =>
      handleUrgentPathOffers(sender(), m.offers)

    case m: SelectUrgentPathsMessage =>
      handleSelectUrgentPaths(m.leafIds)

    case UrgentPathsSelectedMessage =>
      handleUrgentPathsSelected()

    // --- measurement collection ---------------------------------------------

    case m: MeasureTemperatureMessage =>
      handleMeasureTemperature(m.measurementId)

    case m: TemperatureReadingMessage =>
      handleTemperatureReading(m.measurementId, m.temperature)

    case m: UrgentUpdateTemperatureMessage =>
      handleUpdateTemperature(m.temperature)

    // --- teardown -----------------------------------------------------------

    case DestroySubtreeMessage =>
      handleDestroySubtree()

    case SubtreeDestroyedMessage =>
      handleSubtreeDestroyed()
  }

  // --- tree construction ----------------------------------------------------

  private def handleCreateSubtree(): Unit =
    plan.expansionOf(id) match {
      case Some(expansion) => createSubtree(expansion)
      case None => signalSubtreeCreated(LeafDistance(id, distance = 0))
    }

  private def createSubtree(expansion: Expansion): Unit = {
    //
    // Create children in the context of this node, so that the actor hierarchy follows
    // the tree topology. Creating all node actors at the top level makes them children
    // of the same guardian actor. This causes massive contention when creating new
    // actors and makes construction of the tree an order of magnitude slower.
    //
    children ++= expansion.childIds(plan.childCount).map { childId =>
      context.actorOf(UctNodeActor.props(childId, plan))
    }

    pendingResponseCount = children.length
    children.foreach(child => child ! CreateSubtreeMessage)
  }

  private def handleSubtreeCreated(
    child: ActorRef,
    childChecksum: TreeChecksum,
    farthestLeaf: LeafDistance
  ): Unit = {
    subtreeChecksum = subtreeChecksum.combinedWith(childChecksum)
    childFarthestLeaves(child) = farthestLeaf

    pendingResponseCount -= 1
    if (pendingResponseCount == 0) {
      // A child measures the leaf distances from itself, so the leaf is
      // one edge farther when measured from this node.
      val (_, farthestLeafFromChild) = LeafDistance.farthestOf(childFarthestLeaves)
      signalSubtreeCreated(farthestLeafFromChild.fartherBy(1))
    }
  }

  private def signalSubtreeCreated(farthestLeaf: LeafDistance): Unit =
    context.parent ! SubtreeCreatedMessage(subtreeChecksum, farthestLeaf)

  // --- urgent path selection ------------------------------------------------

  private def handleCollectUrgentPathOffers(
    branchDistance: Int,
    leafDistanceMin: Int,
    offerCountMax: Int
  ): Unit = {
    urgentPathOffers.clear()
    urgentPathOfferChildren.clear()
    urgentPathOfferCountMax = offerCountMax

    if (branchDistance == 0) {
      offerChildFarthestLeaves(leafDistanceMin)
      signalUrgentPathOffers()
    } else if (urgentChildren.isEmpty) {
      // A leaf ending an urgent path above the branching nodes has nothing to offer.
      signalUrgentPathOffers()
    } else {
      pendingResponseCount = urgentChildren.size
      urgentChildren.foreach { urgentChild =>
        urgentChild ! CollectUrgentPathOffersMessage(
          branchDistance - 1,
          leafDistanceMin - 1,
          offerCountMax
        )
      }
    }
  }

  private def offerChildFarthestLeaves(leafDistanceMin: Int): Unit =
    childFarthestLeaves.foreach { (child, farthestLeaf) =>
      // The offer is measured from this node, one edge above the child.
      val offer = farthestLeaf.fartherBy(1)
      if (!urgentChildren.contains(child) && offer.distance >= leafDistanceMin) {
        addUrgentPathOffer(child, offer)
      }
    }

  private def handleUrgentPathOffers(child: ActorRef, offers: Seq[LeafDistance]): Unit = {
    offers.foreach(offer => addUrgentPathOffer(child, offer))

    pendingResponseCount -= 1
    if (pendingResponseCount == 0) {
      signalUrgentPathOffers()
    }
  }

  private def addUrgentPathOffer(child: ActorRef, offer: LeafDistance): Unit = {
    urgentPathOffers += offer
    urgentPathOfferChildren(offer.leafId) = child
  }

  private def signalUrgentPathOffers(): Unit =
    context.parent ! UrgentPathOffersMessage(
      urgentPathOffers.sorted.take(urgentPathOfferCountMax).toSeq
    )

  /**
   * Forwards each selected leaf to the child on its path. At the branching node that
   * offered the leaf in the current round, that child is recorded in
   * [[urgentPathOfferChildren]]; at nodes below the branching node, the offered leaf
   * is always reached through the child with the farthest leaf.
   */
  private def handleSelectUrgentPaths(leafIds: Seq[NodeId]): Unit = {
    if (children.isEmpty) {
      signalUrgentPathsSelected()
    } else {
      val leafIdsByChild = leafIds.groupBy { leafId =>
        urgentPathOfferChildren.getOrElse(leafId, farthestLeafChild)
      }

      pendingResponseCount = leafIdsByChild.size
      leafIdsByChild.foreach { (child, childLeafIds) =>
        urgentChildren += child
        child ! SelectUrgentPathsMessage(childLeafIds)
      }
    }
  }

  private def farthestLeafChild: ActorRef = {
    val (child, _) = LeafDistance.farthestOf(childFarthestLeaves)
    child
  }

  private def handleUrgentPathsSelected(): Unit = {
    pendingResponseCount -= 1
    if (pendingResponseCount == 0) {
      signalUrgentPathsSelected()
    }
  }

  private def signalUrgentPathsSelected(): Unit =
    context.parent ! UrgentPathsSelectedMessage

  // --- measurement collection -----------------------------------------------

  private def handleMeasureTemperature(measurementId: MeasurementId): Unit = {
    if (children.isEmpty) {
      // Leaf: initialize temperature on first measurement, then report.
      if (temperature.isEmpty) {
        temperature = Some(LeafNode.initialTemperatureOf(id))
      }

      signalTemperatureReading(measurementId, temperature.get)
    } else {
      // Interior: scatter to children and gather replies.
      pendingMeasurements(measurementId) =
        UctNodeActor.Measurement(temperatureSum = 0.0, children.length)

      children.foreach(child => child ! MeasureTemperatureMessage(measurementId))
    }
  }

  private def handleTemperatureReading(
    measurementId: MeasurementId,
    temperatureReading: Double
  ): Unit = {
    val measurement = pendingMeasurements(measurementId).withReading(temperatureReading)
    if (measurement.isComplete) {
      pendingMeasurements.remove(measurementId)
      signalTemperatureReading(measurementId, measurement.temperatureSum / children.length)
    } else {
      pendingMeasurements(measurementId) = measurement
    }
  }

  private def signalTemperatureReading(
    measurementId: MeasurementId,
    temperature: Double
  ): Unit =
    context.parent ! TemperatureReadingMessage(measurementId, temperature)

  /**
   * Propagates temperature update down the urgent paths; at a leaf, applies it directly.
   * Processed before any queued [[MeasureTemperatureMessage]] because
   * [[UrgentUpdateTemperatureMessage]] extends ControlMessage.
   */
  private def handleUpdateTemperature(newTemperature: Double): Unit = {
    if (children.isEmpty) {
      temperature = Some(newTemperature)
    } else {
      urgentChildren.foreach { urgentChild =>
        urgentChild ! UrgentUpdateTemperatureMessage(newTemperature)
      }
    }
  }

  // --- teardown -------------------------------------------------------------
  //
  // Teardown mirrors the build protocol. Leaves stop and signal their parent.
  // Interior nodes cascade DestroySubtreeMessage to all children and wait for all
  // replies before stopping and signaling upward.

  private def handleDestroySubtree(): Unit = {
    if (children.isEmpty) {
      context.stop(self)
      signalSubtreeDestroyed()
    } else {
      pendingResponseCount = children.length
      children.foreach(child => child ! DestroySubtreeMessage)
    }
  }

  private def handleSubtreeDestroyed(): Unit = {
    pendingResponseCount -= 1
    if (pendingResponseCount == 0) {
      context.stop(self)
      signalSubtreeDestroyed()
    }
  }

  private def signalSubtreeDestroyed(): Unit =
    context.parent ! SubtreeDestroyedMessage
}
