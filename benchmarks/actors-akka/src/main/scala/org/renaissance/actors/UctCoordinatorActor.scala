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
 *
 * The coordinator also runs the urgent path selection. It makes the same selection as
 * [[UctUrgentPathSelector]], but in rounds:
 *
 * - The first urgent path leads to the leaf farthest from the root.
 * - Round `d` selects the paths that branch off the selected ones at depth `d`. Each node
 *   on an urgent path at depth `d` offers, for each of its children that is not on an
 *   urgent path, the leaf farthest from that child. The coordinator selects the best of
 *   these offers, up to the number of paths left to select.
 *
 * Each child offers a single leaf per round, the one farthest from it, with the smallest
 * ID among equally far leaves, because the selection prefers longer paths, and among
 * equally long paths the one ending in the leaf with the smallest ID. Once a path through
 * a child is selected, the other paths through that child overlap more with the selected
 * ones and wait for a later round.
 *
 * Each selection is acknowledged before the next round, so that all urgent paths are
 * recorded before the urgent update, which could otherwise overtake a selection waiting
 * in a mailbox.
 */
private[actors] final class UctCoordinatorActor(topology: Topology) extends Actor {

  private var rootNode: ActorRef = _

  // The leaf farthest from the root, reported by the root when the tree is built. Its
  // distance from the root is the tree height.
  private var treeFarthestLeaf: LeafDistance = _

  // State of the urgent path selection: the leaves ending the paths selected so far, the
  // number of paths to select, the minimum path length, and the depth of the next round.
  private val urgentLeafIds = mutable.ListBuffer[NodeId]()
  private var urgentPathCount: Int = 0
  private var urgentPathLengthMin: Int = 0
  private var branchDepth: Int = 0

  // Fulfilled when each phase completes. Measurements are identified by IDs assigned
  // in the order in which they are requested.
  private var uctCreatedPromise: Promise[Unit] = _
  private var urgentPathsSelectedPromise: Promise[Seq[NodeId]] = _
  private val measurementPromises = mutable.Map[MeasurementId, Promise[Double]]()
  private var nextMeasurementId: MeasurementId = MeasurementId.First
  private var uctDestroyedPromise: Promise[Unit] = _

  override def receive: Receive = {
    // --- tree construction --------------------------------------------------

    case LocalCreateUctMessage(completionPromise) =>
      uctCreatedPromise = completionPromise
      rootNode = context.actorOf(UctNodeActor.props(NodeId.Root, topology))
      rootNode ! CreateSubtreeMessage

    case m: SubtreeCreatedMessage =>
      treeFarthestLeaf = m.farthestLeaf
      uctCreatedPromise.success(())

    // --- urgent path selection ----------------------------------------------

    case LocalSelectUrgentPathsMessage(pathCount, pathLengthFractionMin, resultPromise) =>
      urgentPathsSelectedPromise = resultPromise
      urgentPathCount = pathCount
      urgentPathLengthMin = UctUrgentPathSelector.pathLengthMinOf(
        treeFarthestLeaf.distance,
        pathLengthFractionMin
      )

      branchDepth = 0
      selectUrgentPaths(Seq(treeFarthestLeaf.leafId))

    case UrgentPathsSelectedMessage =>
      collectUrgentPathOffers()

    case m: UrgentPathOffersMessage =>
      branchDepth += 1
      if (m.offers.isEmpty) {
        collectUrgentPathOffers()
      } else {
        selectUrgentPaths(m.offers.map(offer => offer.leafId))
      }

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

  // --- urgent path selection ------------------------------------------------

  private def selectUrgentPaths(leafIds: Seq[NodeId]): Unit = {
    urgentLeafIds ++= leafIds
    rootNode ! SelectUrgentPathsMessage(leafIds)
  }

  /**
   * Starts the next round, or completes the selection when there are no paths left to
   * select or no nodes below the depth of the next round.
   */
  private def collectUrgentPathOffers(): Unit = {
    val remainingPathCount = urgentPathCount - urgentLeafIds.length
    if (remainingPathCount == 0 || branchDepth == treeFarthestLeaf.distance) {
      urgentPathsSelectedPromise.success(urgentLeafIds.toList)
    } else {
      // Counted from the root, distances are depths, and leaf distances are path lengths.
      rootNode ! CollectUrgentPathOffersMessage(
        branchDistance = branchDepth,
        leafDistanceMin = urgentPathLengthMin,
        offerCountMax = remainingPathCount
      )
    }
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
