package org.renaissance.actors

/** Node identifier: a contiguous integer assigned during tree generation (root = 0). */
type NodeId = Int

/**
 * Describes an interior (non-leaf) node in the pre-computed tree.
 *
 * @param firstChildId node ID of the first child;
 *   children occupy firstChildId .. firstChildId+branchingFactor-1
 * @param urgentChildSlots set of 0-based child slot indices on urgent paths through this node;
 *   empty means this node is not on any urgent path
 */
case class InteriorNode(
  firstChildId: NodeId,
  urgentChildSlots: Set[Int] = Set.empty
)

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
case class Topology(
  interiorNodes: Map[NodeId, InteriorNode],
  nodeCount: Int,
  maxDepth: Int
)
