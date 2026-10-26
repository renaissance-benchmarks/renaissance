package org.renaissance.actors

/**
 * Pre-computed expansion decisions of interior nodes. Each node looks up its own
 * expansion when asked to create its subtree. Stands in for a random choice each
 * node would make locally, which would make the actor topologies non-repeatable.
 * Contains only what actors need to build the particular UCT topology.
 *
 * @param interiorNodes nodeId -> Expansion (only) for nodes that expand
 * @param childCount number of children of every expanding node
 */
private[actors] final class ExpansionPlan private (
  interiorNodes: Map[NodeId, Expansion],
  val childCount: Int
) {

  /** How the given node expands, or None if it stays a leaf. */
  def expansionOf(nodeId: NodeId): Option[Expansion] = interiorNodes.get(nodeId)
}

private[actors] object ExpansionPlan {

  /** Produces an [[ExpansionPlan]] for the given [[Topology]]. */
  def of(topology: Topology): ExpansionPlan =
    new ExpansionPlan(topology.interiorNodes, topology.branchingFactor)
}
