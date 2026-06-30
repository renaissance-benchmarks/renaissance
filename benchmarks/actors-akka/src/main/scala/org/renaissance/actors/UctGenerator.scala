package org.renaissance.actors

import java.util.Random
import scala.collection.mutable

/**
 * Builds a random tree topology to be represented using actors.
 *
 * Built single-threaded using the provided RNG — identical output for identical seeds.
 * The tree is purely random: each frontier node gets a coin flip (expand or
 * leaf), processed FIFO until the node budget is exhausted.
 *
 * Actors look up the resulting immutable maps instead of making random
 * decisions at runtime, removing the dependency on non-deterministic
 * message ordering.
 */
final class UctGenerator(
  nodeCountMax: Int,
  branchingFactor: Int,
  rng: Random
) {

  private val interiorNodes = mutable.Map[NodeId, InteriorNode]()
  private val frontier = mutable.ArrayBuffer[(NodeId, Int)]()

  private var size = 1 // root is node 0
  private var maxDepth = 0

  def build(): Topology = {
    expandRoot()
    expandFrontier()
    Topology(interiorNodes = interiorNodes.toMap, nodeCount = size, maxDepth = maxDepth)
  }

  // Root always expands; urgentChildSlots will be filled by the strategy.
  private def expandRoot(): Unit = {
    interiorNodes(0) = InteriorNode(
      firstChildId = size,
      urgentChildSlots = Set.empty
    )
    addChildren(startId = size, startDepth = 1)
    size += branchingFactor
    maxDepth = 1
  }

  // FIFO expansion: each frontier node gets a coin flip — expand or become a leaf.
  private def expandFrontier(): Unit = {
    while (frontier.nonEmpty) {
      val (nodeId, depth) = frontier.remove(0)
      if (canExpand && rng.nextBoolean()) {
        expandNode(nodeId, depth)
      }
      // else: node becomes a leaf — not inserted into interiorNodes.
    }
  }

  private def expandNode(nodeId: NodeId, depth: Int): Unit = {
    interiorNodes(nodeId) = InteriorNode(size, urgentChildSlots = Set.empty)
    val childDepth = depth + 1
    addChildren(startId = size, startDepth = childDepth)
    size += branchingFactor
    if (childDepth > maxDepth) maxDepth = childDepth
  }

  private def addChildren(startId: NodeId, startDepth: Int): Unit = {
    for (i <- 0 until branchingFactor) {
      frontier += ((startId + i, startDepth))
    }
  }

  private def canExpand: Boolean = size + branchingFactor <= nodeCountMax
}
