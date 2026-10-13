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
  def props(id: NodeId, topology: Topology): Props = Props(new UctNodeActor(id, topology))

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
private[actors] final class UctNodeActor(id: NodeId, topology: Topology) extends Actor {

  // Tree structure, populated during the build phase, with the children on urgent paths.
  private val children: mutable.Buffer[ActorRef] = mutable.Buffer.empty
  private val urgentChildren = mutable.Set[ActorRef]()

  // Pending-response counter, reused across the build and teardown phases.
  private var pendingResponseCount: Int = 0

  // Temperature state
  private var temperature: Option[Double] = None

  // Measurements still waiting for readings from the children.
  private val pendingMeasurements = mutable.Map[MeasurementId, UctNodeActor.Measurement]()

  override def receive: Receive = {
    // --- tree construction --------------------------------------------------

    case CreateSubtreeMessage =>
      handleCreateSubtree()

    case SubtreeCreatedMessage =>
      handleSubtreeCreated()

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
    topology.interiorNodes.get(id) match {
      case Some(node) => createSubtree(node)
      case None => signalSubtreeCreated()
    }

  private def createSubtree(node: InteriorNode): Unit = {
    //
    // Create children in the context of this node, so that the actor hierarchy follows
    // the tree topology. Creating all node actors at the top level makes them children
    // of the same guardian actor. This causes massive contention when creating new
    // actors and makes construction of the tree an order of magnitude slower.
    //
    children ++= node.childIds(topology.branchingFactor).map { childId =>
      context.actorOf(UctNodeActor.props(childId, topology))
    }
    urgentChildren ++= node.urgentChildSlots.map(children)

    pendingResponseCount = children.length
    children.foreach(child => child ! CreateSubtreeMessage)
  }

  private def handleSubtreeCreated(): Unit = {
    pendingResponseCount -= 1
    if (pendingResponseCount == 0) {
      signalSubtreeCreated()
    }
  }

  private def signalSubtreeCreated(): Unit =
    context.parent ! SubtreeCreatedMessage

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
