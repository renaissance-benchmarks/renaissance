package org.renaissance.actors

/**
 * The tree structure passed to actors at runtime.
 *
 * Contains only what actors need to execute the workload — no information
 * about which leaves are urgent, so benchmark code cannot accidentally
 * depend on urgent selection results during execution.
 *
 * @param interiorNodes nodeId -> InteriorNode for nodes that expand.
 *   If a nodeId is absent, the node is a leaf.
 * @param nodeCount total number of nodes in the tree
 * @param maxDepth depth of the deepest leaf (root = 0)
 */
private[actors] final case class Topology(
  interiorNodes: Map[NodeId, InteriorNode],
  nodeCount: Int,
  maxDepth: Int
)
