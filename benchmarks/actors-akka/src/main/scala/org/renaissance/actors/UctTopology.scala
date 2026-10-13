package org.renaissance.actors

/**
 * The structure of a pre-computed tree.
 *
 * - The **depth** of a node is its distance (number of edges) to the root
 *   (which has depth 0).
 * - The length of a path from the root to some leaf is the depth of that leaf.
 * - The **height** of a tree is the length of its longest root-to-leaf path,
 *   and the tree has `height + 1` **levels**.
 *
 * @param interiorNodes nodeId -> InteriorNode for nodes that expand
 * @param leafDepths nodeId -> depth (root = 0) for nodes that stay leaves
 * @param branchingFactor number of children of every interior node
 */
private[actors] final case class Topology(
  interiorNodes: Map[NodeId, InteriorNode],
  leafDepths: Map[NodeId, Int],
  branchingFactor: Int
) {

  /** Total number of nodes in the tree. */
  val nodeCount: Int = interiorNodes.size + leafDepths.size

  /** Height of the tree: the length of the longest root-to-leaf path. */
  val height: Int = leafDepths.values.max

  /**
   * Reduces the tree bottom-up: [[leaf]] assigns a value to each leaf node; [[combine]]
   * computes the value of an interior node from the values of its children (in child-slot
   * order).
   */
  def fold[A](leaf: NodeId => A)(combine: IndexedSeq[A] => A): A = {
    def go(id: NodeId): A = interiorNodes.get(id) match {
      case None => leaf(id)
      case Some(node) =>
        combine(node.childIds(branchingFactor).map(go))
    }

    go(NodeId.Root)
  }
}
