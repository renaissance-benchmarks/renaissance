package org.renaissance.actors

import akka.actor.Actor
import akka.actor.ActorRef
import akka.actor.ActorSystem
import akka.actor.Props

import scala.concurrent.Promise

import UctConfig.*

// -------------------------------------------------------------------------
//  UctRootActor
// -------------------------------------------------------------------------

private[actors] class UctRootActor(
  topology: Topology,
  shockTemperature: Double,
  resultPromise: Promise[Double]
) extends Actor {

  private val rootNode = topology.interiorNodes(0)

  private val children = new Array[ActorRef](BranchingFactor)

  // Build and teardown phases: count down SubtreeCreated/SubtreeDestroyed messages.
  private var pendingChildCount = 0

  // Collection phase
  private var currentReduction = 0
  private var pendingMeasurementCount = 0
  private var temperatureAccumulator: Double = 0.0
  private var temperature: Double = 0.0

  override def receive: Receive = {
    case GenerateTreeMessage =>
      handleGenerateTree()

    case m: ExpansionQueryMessage =>
      handleExpansionQuery(m.sender, m.senderId)

    case SubtreeCreatedMessage =>
      handleSubtreeCreated()

    case m: TemperatureReadingMessage =>
      handleTemperatureReading(m.temperature)

    case TerminateMessage =>
      handleTerminate()

    case SubtreeDestroyedMessage =>
      handleSubtreeDestroyed()

    case _ =>
  }

  // --- build --------------------------------------------------------------

  private def handleGenerateTree(): Unit = {
    val urgentChildSlots = rootNode.urgentChildSlots

    var slot = 0
    while (slot < BranchingFactor) {
      children(slot) = UctNodeActor.create(
        context.system,
        self,
        id = rootNode.firstChildId + slot,
        childSlot = slot,
        urgent = urgentChildSlots.contains(slot),
        topology = topology
      )

      slot += 1
    }

    pendingChildCount = BranchingFactor

    slot = 0
    while (slot < BranchingFactor) {
      children(slot) ! CheckExpansionMessage
      slot += 1
    }
  }

  private def handleExpansionQuery(sender: ActorRef, nodeId: NodeId): Unit =
    topology.interiorNodes.get(nodeId) match {
      case Some(node) =>
        sender ! CreateChildrenMessage(node.firstChildId, node.urgentChildSlots)
      case None => sender ! StayLeafMessage
    }

  private def handleSubtreeCreated(): Unit = {
    pendingChildCount -= 1
    if (pendingChildCount == 0) {
      startNextReduction()
    }
  }

  // --- collection ---------------------------------------------------------

  private def startNextReduction(): Unit = {
    currentReduction += 1
    pendingMeasurementCount = BranchingFactor
    temperatureAccumulator = 0.0

    if (currentReduction == ReductionCount) {
      // Shock reduction: send UrgentUpdateTemperature (ControlMessage) to every urgent
      // child *before* the normal MeasureTemperature.  With a priority mailbox the
      // urgent update jumps ahead of MeasureTemperature at every hop down every urgent
      // path.
      val urgentChildSlots = rootNode.urgentChildSlots
      var slot = 0
      while (slot < BranchingFactor) {
        children(slot) ! MeasureTemperatureMessage

        if (urgentChildSlots.contains(slot)) {
          children(slot) ! UrgentUpdateTemperatureMessage(shockTemperature)
        }

        slot += 1
      }
    } else {
      var slot = 0
      while (slot < BranchingFactor) {
        children(slot) ! MeasureTemperatureMessage
        slot += 1
      }
    }
  }

  private def handleTemperatureReading(temperatureReading: Double): Unit = {
    temperatureAccumulator += temperatureReading
    pendingMeasurementCount -= 1

    if (pendingMeasurementCount == 0) {
      temperature = temperatureAccumulator / BranchingFactor

      if (currentReduction < ReductionCount) {
        startNextReduction()
      } else {
        handleTerminate()
      }
    }
  }

  // --- termination --------------------------------------------------------

  private def handleTerminate(): Unit = {
    pendingChildCount = BranchingFactor
    var slot = 0
    while (slot < BranchingFactor) {
      children(slot) ! TerminateMessage
      slot += 1
    }
  }

  private def handleSubtreeDestroyed(): Unit = {
    pendingChildCount -= 1
    if (pendingChildCount == 0) {
      context.stop(self)
      // All child actors have stopped before the promise is fulfilled, so
      // system.terminate() in runIteration cannot race with in-flight messages.
      resultPromise.success(temperature)
    }
  }
}

// -------------------------------------------------------------------------
//  UctNodeActor
// -------------------------------------------------------------------------

private[actors] object UctNodeActor {

  def create(
    system: ActorSystem,
    parent: ActorRef,
    id: NodeId,
    childSlot: Int,
    urgent: Boolean,
    topology: Topology
  ): ActorRef =
    system.actorOf(
      Props(new UctNodeActor(parent, id, childSlot, urgent, topology))
    )
}

private[actors] class UctNodeActor(
  parent: ActorRef,
  id: NodeId,
  childSlot: Int,
  isUrgent: Boolean,
  topology: Topology
) extends Actor {

  // Tree structure (populated during build phase)
  private var urgentChildSlots: Set[Int] = Set.empty
  private var hasChildren: Boolean = false
  private val children = new Array[ActorRef](BranchingFactor)
  private var pendingChildCount: Int = 0

  // Temperature state
  private var temperature: Double = 0.0
  private var temperatureInitialized: Boolean = false
  private var temperatureAccumulator: Double = 0.0
  private var pendingMeasurementCount: Int = 0

  override def receive: Receive = {
    // Build phase
    case CheckExpansionMessage =>
      parent ! ExpansionQueryMessage(self, id)

    case m: ExpansionQueryMessage =>
      handleExpansionQuery(m.sender, m.senderId)

    case m: CreateChildrenMessage =>
      createSubtree(m.firstChildId, m.urgentChildSlots)

    case StayLeafMessage =>
      signalSubtreeCreated()

    case SubtreeCreatedMessage =>
      handleSubtreeCreated()

    // Collection phase
    case MeasureTemperatureMessage =>
      handleMeasureTemperature()

    case m: TemperatureReadingMessage =>
      handleTemperatureReading(m.temperature)

    case m: UrgentUpdateTemperatureMessage =>
      handleUpdateTemperature(m.temperature)

    // Termination
    case TerminateMessage =>
      handleTerminate()

    case SubtreeDestroyedMessage =>
      handleSubtreeDestroyed()

    case _ =>
  }

  // --- build --------------------------------------------------------------

  private def handleExpansionQuery(child: ActorRef, childId: NodeId): Unit =
    topology.interiorNodes.get(childId) match {
      case Some(node) =>
        child ! CreateChildrenMessage(node.firstChildId, node.urgentChildSlots)
      case None => child ! StayLeafMessage
    }

  private def createSubtree(firstChildId: NodeId, childUrgentSlots: Set[Int]): Unit = {
    urgentChildSlots = childUrgentSlots

    var slot = 0
    while (slot < BranchingFactor) {
      children(slot) = UctNodeActor.create(
        context.system,
        self,
        id = firstChildId + slot,
        childSlot = slot,
        urgent = childUrgentSlots.contains(slot),
        topology = topology
      )
      slot += 1
    }

    hasChildren = true
    pendingChildCount = BranchingFactor

    slot = 0
    while (slot < BranchingFactor) {
      children(slot) ! CheckExpansionMessage
      slot += 1
    }
  }

  private def handleSubtreeCreated(): Unit = {
    pendingChildCount -= 1
    if (pendingChildCount == 0) {
      signalSubtreeCreated()
    }
  }

  private def signalSubtreeCreated(): Unit =
    parent ! SubtreeCreatedMessage

  // --- collection ---------------------------------------------------------

  private def handleMeasureTemperature(): Unit = {
    if (!hasChildren) {
      // Leaf: initialize temperature on first reduction, then report.
      if (!temperatureInitialized) {
        temperature = AkkaUct.leafInitialTemperature(id, LeafTemperatureSeed)
        temperatureInitialized = true
      }

      signalCollectionResult(temperature)

    } else {
      // Interior node: scatter the reduction to all children; gather replies.
      pendingMeasurementCount = BranchingFactor
      temperatureAccumulator = 0.0

      var slot = 0
      while (slot < BranchingFactor) {
        children(slot) ! MeasureTemperatureMessage
        slot += 1
      }
    }
  }

  private def handleTemperatureReading(temperatureReading: Double): Unit = {
    temperatureAccumulator += temperatureReading
    pendingMeasurementCount -= 1

    if (pendingMeasurementCount == 0) {
      temperature = temperatureAccumulator / BranchingFactor
      signalCollectionResult(temperature)
    }
  }

  private def signalCollectionResult(temperature: Double): Unit =
    parent ! TemperatureReadingMessage(temperature)

  /**
   * Urgent: propagate the temperature update down all urgent paths, or apply it at a leaf.
   *
   * With a working priority mailbox this message is processed *before* any
   * pending [[MeasureTemperatureMessage]] in the same mailbox, so the leaf's
   * temperature is updated before it responds to the reduction.
   */
  private def handleUpdateTemperature(newTemperature: Double): Unit = {
    if (!hasChildren) {
      temperature = newTemperature
      temperatureInitialized = true
    } else {
      for (slot <- urgentChildSlots) {
        children(slot) ! UrgentUpdateTemperatureMessage(newTemperature)
      }
    }
  }

  // --- termination --------------------------------------------------------
  //
  // Teardown mirrors the build protocol. Leaves stop and signal their parent.
  // Interior nodes cascade TerminateMessage to all children and wait for all
  // replies before stopping and signaling upward.
  //
  // Do NOT replace with Future.sequence over per-child promises. Future callbacks
  // run on the dispatcher thread pool (outside receive), so they race with the
  // actor's own state and violate Akka's single-thread guarantee.

  private def handleTerminate(): Unit = {
    if (hasChildren) {
      pendingChildCount = BranchingFactor
      var slot = 0
      while (slot < BranchingFactor) {
        children(slot) ! TerminateMessage
        slot += 1
      }
    } else {
      context.stop(self)
      signalSubtreeDestroyed()
    }
  }

  private def handleSubtreeDestroyed(): Unit = {
    pendingChildCount -= 1
    if (pendingChildCount == 0) {
      context.stop(self)
      signalSubtreeDestroyed()
    }
  }

  private def signalSubtreeDestroyed(): Unit =
    parent ! SubtreeDestroyedMessage
}
