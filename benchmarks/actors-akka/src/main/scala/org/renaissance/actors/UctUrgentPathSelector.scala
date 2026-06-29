package org.renaissance.actors

import scala.collection.mutable

/**
 * Greedy urgent-path selection strategy.
 *
 * Selects `urgentPathCount` deep leaves that maximize pairwise path divergence —
 * i.e. their paths from the root share the shortest possible common prefix.
 *
 * Only leaves at depth >= maxHeight * depthThreshold are considered; if none
 * qualify, the threshold is ignored and all leaves are eligible.
 *
 * Selection algorithm:
 *   - Seed with the globally deepest leaf.
 *   - Each subsequent pick is the candidate that minimizes its maximum LCA depth
 *     with all already-selected paths (minimax divergence).
 *
 * @param urgentPathCount  how many urgent leaves to select
 * @param urgentLeafDepthFractionMin   fraction of maxDepth below which leaves are excluded
 */
final class UctUrgentPathSelector(
  urgentPathCount: Int,
  urgentLeafDepthFractionMin: Double
) {

  def selectUrgentPaths(
    interiorNodes: Map[NodeId, InteriorNode],
    branchingFactor: Int,
    maxDepth: Int
  ): (Map[NodeId, InteriorNode], List[NodeId]) = {

    // Map [nodeId, depth of node]
    val depthOf = buildDepthMap(interiorNodes, branchingFactor)
    // Map [childId, parentId]
    val parentOf = buildParentMap(interiorNodes, branchingFactor)

    // Memoized root-first path lookup: avoids recomputing shared prefixes.
    // Map [leafId, path of leafIds from root to leaf]
    val pathCache = mutable.Map[NodeId, Array[NodeId]]()
    def rootPath(nodeId: NodeId): Array[NodeId] =
      pathCache.getOrElseUpdate(nodeId, buildRootPath(nodeId, parentOf))

    // candidates are only leaves
    val candidates = collectCandidates(depthOf, interiorNodes, maxDepth)
    val (selectedLeaves, selectedPaths) = greedySelectLeaves(candidates, rootPath)

    val annotatedInteriorNodes = annotateUrgentChildSlots(interiorNodes, selectedPaths)
    (annotatedInteriorNodes, selectedLeaves)
  }

  /**
   * Step 1: BFS from root to build a nodeId -> depth map.
   *
   * Seeds the root at depth 0, then for every interior node assigns
   * depth(child) = depth(parent) + 1.
   */
  private def buildDepthMap(
    interiorNodes: Map[NodeId, InteriorNode],
    branchingFactor: Int
  ): mutable.Map[NodeId, Int] = {
    val depthOf = mutable.Map[NodeId, Int](0 -> 0)
    val bfsQueue = mutable.Queue[NodeId](0)

    while (bfsQueue.nonEmpty) {
      val nodeId = bfsQueue.dequeue()
      interiorNodes.get(nodeId).foreach { node =>
        var childSlot = 0
        while (childSlot < branchingFactor) {
          val childId = node.firstChildId + childSlot
          depthOf(childId) = depthOf(nodeId) + 1
          bfsQueue.enqueue(childId)
          childSlot += 1
        }
      }
    }
    depthOf
  }

  /**
   * Step 2: Build a reverse lookup from each child node ID to its parent node ID.
   *
   * Children are stored as a contiguous block starting at firstChildId,
   * so child at slot j has nodeId = firstChildId + j, parent = parentId.
   */
  private def buildParentMap(
    interiorNodes: Map[NodeId, InteriorNode],
    branchingFactor: Int
  ): mutable.Map[NodeId, NodeId] = {
    val parentOf = mutable.Map[NodeId, NodeId]()
    for ((parentId, node) <- interiorNodes; childSlot <- 0 until branchingFactor) {
      parentOf(node.firstChildId + childSlot) = parentId
    }
    parentOf
  }

  /**
   * Step 3: Collect leaf candidates filtered by depth threshold, sorted deepest first.
   *
   * A leaf is any node present in depthOf but absent from interiorNodes (no children).
   * Candidates below minDepth are excluded to ensure urgent paths are non-trivial;
   * if no candidates survive the filter, the threshold is relaxed and all leaves qualify.
   * Ties in depth are broken by nodeId for full determinism.
   */
  private def collectCandidates(
    depthOf: mutable.Map[NodeId, Int],
    interiorNodes: Map[NodeId, InteriorNode],
    maxDepth: Int
  ): Array[NodeId] = {
    val allLeafIds = depthOf.keys.filter(nodeId => !interiorNodes.contains(nodeId)).toArray
    val minDepth = math.max(1, math.ceil(maxDepth * urgentLeafDepthFractionMin).toInt)
    val filtered = allLeafIds.filter(nodeId => depthOf(nodeId) >= minDepth)
    val candidates = if (filtered.nonEmpty) filtered else allLeafIds
    candidates.sortBy(nodeId => (-depthOf(nodeId), nodeId))
  }

  /**
   * Step 4: Walk up from a node to the root via parentOf, building a root-first path.
   *
   * The loop prepends each node as it walks up, so the resulting list is
   * already in root-to-leaf order. The root itself (no parent) is prepended last.
   */
  private def buildRootPath(
    nodeId: NodeId,
    parentOf: mutable.Map[NodeId, NodeId]
  ): Array[NodeId] = {
    var path = List[NodeId]()
    var current = nodeId
    while (parentOf.contains(current)) {
      path = current :: path
      current = parentOf(current)
    }
    // current is now the root (0) — it has no entry in parentOf.
    (current :: path).toArray
  }

  /**
   * Step 5: Greedy leaf selection seeded with the globally deepest candidate.
   *
   * For each subsequent pick, scores every remaining candidate by its maximum
   * LCA depth with all already-selected paths (worst-case overlap), then picks
   * the candidate with the lowest such score (minimize the worst overlap).
   *
   * Returns parallel buffers of selected leaf IDs and their root-first paths.
   */
  private def greedySelectLeaves(
    sortedCandidates: Array[NodeId],
    rootPath: NodeId => Array[NodeId]
  ): (List[NodeId], List[Array[NodeId]]) = {

    val selectCount = math.min(urgentPathCount, sortedCandidates.length)
    val selected = mutable.ArrayBuffer[NodeId]()
    val selectedPaths = mutable.ArrayBuffer[Array[NodeId]]()
    val available = mutable.ArrayBuffer(sortedCandidates: _*)

    // Seed: the globally deepest leaf (sortedCandidates is deepest-first).
    selected += available.remove(0)
    selectedPaths += rootPath(selected(0))

    while (selected.length < selectCount && available.nonEmpty) {
      var bestCandidateIndex = 0
      var bestScore = Int.MaxValue

      var availableIndex = 0
      while (availableIndex < available.length) {
        val candidatePath = rootPath(available(availableIndex))

        // Score = maximum LCA depth with any already-selected path.
        // Higher score means closer to the selected group — worse candidate.
        var score = 0
        for (selectedPath <- selectedPaths) {
          val lcaDepth = computeLcaDepth(candidatePath, selectedPath)
          if (lcaDepth > score) {
            score = lcaDepth
          }
        }

        if (score < bestScore) {
          bestScore = score
          bestCandidateIndex = availableIndex
        }
        availableIndex += 1
      }

      val pickedLeaf = available.remove(bestCandidateIndex)
      selected += pickedLeaf
      selectedPaths += rootPath(pickedLeaf)
    }

    (selected.toList, selectedPaths.toList)
  }

  /**
   * Computes the 0-based depth index of the lowest common ancestor of two nodes,
   * given their root-first paths.
   *
   * Walks both paths in lockstep from the root; stops at the first divergence.
   * The last matching index is the LCA depth.
   */
  private def computeLcaDepth(pathA: Array[NodeId], pathB: Array[NodeId]): Int = {
    val commonLength = math.min(pathA.length, pathB.length)
    var index = 0
    var lcaDepth = 0
    while (index < commonLength && pathA(index) == pathB(index)) {
      lcaDepth = index
      index += 1
    }
    lcaDepth
  }

  /**
   * Step 6: For every selected urgent leaf, walk its root-first path and mark
   * the child direction at each node as urgent; returns a new map with the
   * annotations applied.
   *
   * childSlot = childId - firstChildId converts a global node ID back to the
   * 0-based slot index that actors use to identify which child is urgent.
   */
  private def annotateUrgentChildSlots(
    interiorNodes: Map[NodeId, InteriorNode],
    selectedPaths: List[Array[NodeId]]
  ): Map[NodeId, InteriorNode] = {
    var nodes = interiorNodes
    for (path <- selectedPaths) {
      var pathIndex = 0
      while (pathIndex < path.length - 1) {
        val nodeId = path(pathIndex)
        val childId = path(pathIndex + 1)
        val node = nodes(nodeId)
        val childSlot = childId - node.firstChildId
        nodes = nodes.updated(
          nodeId,
          node.copy(urgentChildSlots = node.urgentChildSlots + childSlot)
        )
        pathIndex += 1
      }
    }
    nodes
  }
}
