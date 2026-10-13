package org.renaissance.actors

import java.util.Random
import scala.collection.mutable

/**
 * Generates a random UCT topology using the provided RNG. At each frontier node,
 * we use the RNG as a coin flip to decide whether the node stays as a leaf or
 * becomes an interior node with a fixed number of children. Frontier nodes are
 * processed in FIFO order until the node budget is exhausted.
 *
 * The topology is used to create an expansion plan that the node actors consult at
 * runtime instead of making random decisions. This makes the generated topologies
 * reproducible, because random numbers are consumed in predictable order. Letting
 * the actors use the RNG (even one with a controlled seed) on their own is subject
 * to non-deterministic scheduling and causes reproducible coin flips to end up in
 * non-reproducible actors.
 */
private[actors] final class UctGenerator(nodeCountMax: Int, branchingFactor: Int) {

  def build(rng: Random): Topology = {
    val interiorNodes = mutable.Map[NodeId, InteriorNode]()

    // The root node is always an interior node with children starting at ID 1.
    val rootNode = addNewNode(NodeId.Root, firstChildId = NodeId.Root + 1, interiorNodes)
    val frontier = mutable.Queue.from(
      rootNode.childIds(branchingFactor).map(childId => (childId, 1))
    )
    val leafDepths = expandFrontier(frontier, interiorNodes, rng)

    Topology(interiorNodes.toMap, leafDepths, branchingFactor)
  }

  private def addNewNode(
    nodeId: NodeId,
    firstChildId: NodeId,
    nodes: mutable.Map[NodeId, InteriorNode]
  ): InteriorNode = {
    val node = InteriorNode(firstChildId)
    nodes(nodeId) = node
    node
  }

  /**
   * Expands the frontier in BFS fashion. Populates the map of interior nodes
   * and returns the depths of the leaf nodes.
   */
  private def expandFrontier(
    frontier: mutable.Queue[(NodeId, Int)],
    interiorNodes: mutable.Map[NodeId, InteriorNode],
    rng: Random
  ): Map[NodeId, Int] = {
    val leafDepths = mutable.Map[NodeId, Int]()

    // Allocated count serves as the next available node ID.
    var allocatedCount = interiorNodes.size + frontier.size
    while (frontier.nonEmpty) {
      val (nodeId, depth) = frontier.dequeue()
      if (allocatedCount + branchingFactor <= nodeCountMax && rng.nextBoolean()) {
        val node = addNewNode(nodeId, firstChildId = NodeId(allocatedCount), interiorNodes)
        frontier.enqueueAll(node.childIds(branchingFactor).map(childId => (childId, depth + 1)))
        allocatedCount += branchingFactor
      } else {
        leafDepths(nodeId) = depth
      }
    }

    leafDepths.toMap
  }
}
