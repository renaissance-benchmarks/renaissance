package org.renaissance.actors

import akka.actor.Actor
import akka.actor.ActorRef

import scala.collection.mutable
import scala.concurrent.Promise

/**
 * Connects the benchmark thread with the actor tree. Receives the local orchestration
 * messages from the benchmark thread, turns them into actor-protocol messages for the
 * root node, and reports completion and/or results through Promises.
 *
 * Towards the root node, the coordinator plays the role of its parent: it receives the
 * reports the root sends upward when a phase completes.
 */
private[actors] final class UctCoordinatorActor(topology: Topology) extends Actor {

  private var rootNode: ActorRef = _

  // Fulfilled when each phase completes. Measurements are identified by IDs assigned
  // in the order in which they are requested.
  private var uctCreatedPromise: Promise[Unit] = _
  private val measurementPromises = mutable.Map[MeasurementId, Promise[Double]]()
  private var nextMeasurementId: MeasurementId = MeasurementId.First
  private var uctDestroyedPromise: Promise[Unit] = _

  override def receive: Receive = {
    // --- tree construction --------------------------------------------------

    case LocalCreateUctMessage(completionPromise) =>
      uctCreatedPromise = completionPromise
      rootNode = context.actorOf(UctNodeActor.props(NodeId.Root, topology))
      rootNode ! CreateSubtreeMessage

    case SubtreeCreatedMessage =>
      uctCreatedPromise.success(())

    // --- measurement collection ---------------------------------------------

    case LocalMeasureTemperatureMessage(resultPromise) =>
      val measurementId = registerMeasurement(resultPromise)
      rootNode ! MeasureTemperatureMessage(measurementId)

    case LocalUrgentUpdateTemperatureMessage(temperature) =>
      // The urgent update follows the measurement requests and overtakes those still
      // waiting in a mailbox along an urgent path (see UrgentUpdateTemperatureMessage).
      rootNode ! UrgentUpdateTemperatureMessage(temperature)

    case m: TemperatureReadingMessage =>
      measurementPromises(m.measurementId).success(m.temperature)

    // --- teardown -----------------------------------------------------------

    case LocalDestroyUctMessage(completionPromise) =>
      uctDestroyedPromise = completionPromise
      rootNode ! DestroySubtreeMessage

    case SubtreeDestroyedMessage =>
      context.stop(self)
      // Completed after all node actors have stopped, so system.terminate() in
      // tearDownAfterEach cannot race with in-flight teardown messages.
      uctDestroyedPromise.success(())
  }

  // --- measurement collection -----------------------------------------------

  /** Registers the Promise of a new measurement under the next measurement ID. */
  private def registerMeasurement(resultPromise: Promise[Double]): MeasurementId = {
    val measurementId = nextMeasurementId
    nextMeasurementId = measurementId.next
    measurementPromises(measurementId) = resultPromise
    measurementId
  }
}
