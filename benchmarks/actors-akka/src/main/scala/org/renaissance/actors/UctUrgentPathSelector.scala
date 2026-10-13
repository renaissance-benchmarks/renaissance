package org.renaissance.actors

import scala.collection.mutable

/**
 * Selects `pathCount` paths from the root to leaves such that the shared path
 * prefix is generally short (with maximum pairwise divergence) and returns the
 * leaf nodes representing the selected paths.
 *
 * The selection prefers the longest paths, because they are used for priority
 * messages and the longer the path, the higher the chance that a priority message
 * overtakes regular messages traveling towards the leaf nodes. The short common
 * prefixes ensure that the priority messages are spread wide.
 *
 * The candidate paths are those with `length >= height * pathLengthFractionMin`
 * (see [[UctUrgentPathSelector.pathLengthMinOf]]).
 *
 * Selection algorithm:
 * - Seed the set of selected paths with the longest path.
 * - Repeatedly add the candidate path that branches off the selected paths closest
 *   to the root, until `pathCount` paths are selected or no candidate path is left.
 *   The overlap of a candidate path with the selected paths is the depth of the deepest
 *   node it shares with any of them, and the added path is the candidate path with the
 *   smallest overlap.
 * - Among candidate paths with the same overlap, add the longest one, and among equally
 *   long ones the one ending in the leaf with the smallest ID.
 *
 * The overlap of a candidate can only grow as more paths are selected. The candidates
 * therefore wait in a priority queue under the overlap computed when they were queued.
 * A candidate taken from the queue is selected if its overlap is still the same, and
 * queued again under the new one otherwise, so the overlap is recomputed only for
 * candidates that are about to be selected.
 *
 * @param pathCount how many paths to select
 * @param pathLengthFractionMin fraction of the tree height below which paths are excluded
 */
private[actors] final class UctUrgentPathSelector(
  pathCount: Int,
  pathLengthFractionMin: Double
) {

  /** Returns the leaves that end the urgent paths, in the order of selection. */
  def selectUrgentLeaves(topology: Topology): List[NodeId] = {
    val pathLengthMin = UctUrgentPathSelector.pathLengthMinOf(
      topology.height,
      pathLengthFractionMin
    )

    val candidatePaths = collectCandidatePaths(topology, pathLengthMin)
    val selectedPaths = greedySelectPaths(candidatePaths)
    selectedPaths.map(path => path.head)
  }

  /**
   * Collects the paths to the leaves at depth `pathLengthMin` or more, ordered
   * so that the longest paths with the lowest leaf ID go first. The paths are
   * leaf-first lists, and the path of a child extends the path of its parent, so
   * the paths share their common parts.
   */
  private def collectCandidatePaths(
    topology: Topology,
    pathLengthMin: Int
  ): IndexedSeq[List[NodeId]] = {
    val candidatePaths = mutable.ArrayBuffer[List[NodeId]]()

    def visit(path: List[NodeId], depth: Int): Unit =
      topology.interiorNodes.get(path.head) match {
        case None =>
          if (depth >= pathLengthMin) {
            candidatePaths += path
          }
        case Some(expansion) =>
          expansion.childIds(topology.branchingFactor).foreach { childId =>
            visit(childId :: path, depth + 1)
          }
      }

    visit(List(NodeId.Root), 0)
    candidatePaths.sortBy(path => (-path.length, path.head)).toIndexedSeq
  }

  /**
   * Greedy path selection seeded with the longest path (the first candidate taken
   * from the queue ordered by longest path and lowest leaf ID).
   *
   * Returns the leaf-first paths of the selected leaves, in the order of selection.
   */
  private def greedySelectPaths(
    candidatePaths: IndexedSeq[List[NodeId]]
  ): List[List[NodeId]] = {
    val selectCount = math.min(pathCount, candidatePaths.length)
    val coveredNodeIds = mutable.Set[NodeId]()
    val selectedPaths = mutable.ListBuffer[List[NodeId]]()

    // Entries are (overlap, candidate index), and the queue yields the smallest entry
    // first. Before any path is selected, every candidate has an overlap of -1.
    val candidateQueue = mutable.PriorityQueue.empty(using Ordering[(Int, Int)].reverse)
    candidateQueue ++= candidatePaths.indices.map(index => (-1, index))

    while (selectedPaths.length < selectCount) {
      val (queuedOverlap, index) = candidateQueue.dequeue()
      val path = candidatePaths(index)
      val overlap = computeOverlap(path, coveredNodeIds)

      if (overlap == queuedOverlap) {
        coveredNodeIds ++= path
        selectedPaths += path
      } else {
        candidateQueue.enqueue((overlap, index))
      }
    }

    selectedPaths.toList
  }

  /**
   * Computes the overlap of a candidate path with the selected paths: the depth
   * of the deepest node it shares with any of them, or -1 if no path is selected.
   * The shared nodes run from the root down to that depth, so the overlap is the
   * number of nodes of the candidate path that the selected paths cover, minus one.
   */
  private def computeOverlap(path: List[NodeId], coveredNodeIds: collection.Set[NodeId]): Int =
    path.count(nodeId => coveredNodeIds.contains(nodeId)) - 1
}

private[actors] object UctUrgentPathSelector {

  /**
   * Minimum length of an urgent path in a tree of the given height: the given fraction of
   * the height, rounded up, but at least 1 and at most the height, so that the longest
   * paths always qualify.
   */
  def pathLengthMinOf(height: Int, pathLengthFractionMin: Double): Int =
    math.ceil(height * pathLengthFractionMin).toInt.max(1).min(height)
}
