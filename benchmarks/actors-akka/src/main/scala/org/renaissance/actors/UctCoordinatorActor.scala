package org.renaissance.actors

import akka.actor.Actor
import akka.actor.ActorRef

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

  // Fulfilled when each phase completes.
  private var uctCreatedPromise: Promise[Unit] = _
  private var measurementPromise: Promise[Double] = _
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
      measurementPromise = resultPromise
      rootNode ! MeasureTemperatureMessage

    case LocalMeasureTemperatureWithUrgentUpdateMessage(temperature, resultPromise) =>
      measurementPromise = resultPromise
      // The urgent update follows the measurement request and overtakes it in every
      // mailbox where both are waiting (see UrgentUpdateTemperatureMessage).
      rootNode ! MeasureTemperatureMessage
      rootNode ! UrgentUpdateTemperatureMessage(temperature)

    case m: TemperatureReadingMessage =>
      measurementPromise.success(m.temperature)

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
}
