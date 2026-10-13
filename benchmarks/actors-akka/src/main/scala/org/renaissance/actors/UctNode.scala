package org.renaissance.actors

/**
 * Unique identifier of a node in the pre-computed tree topology.
 * Defined as an opaque type to restrict its use as an integer, with
 * a `+` operation to produce offset identifiers.
 * Nodes are numbered contiguously starting from 0 (root).
 */
opaque private[actors] type NodeId = Int

private[actors] object NodeId {

  /** The root node of every topology. */
  val Root: NodeId = 0

  def apply(n: Int): NodeId = n

  extension (id: NodeId) {
    def toLong: Long = id.toLong
    def +(offset: Int): NodeId = id + offset
  }

  given ordering: Ordering[NodeId] = Ordering.Int
}

/**
 * Describes an interior (non-leaf) node in the pre-computed tree.
 *
 * @param firstChildId node ID of the first child;
 *   children occupy firstChildId .. firstChildId+branchingFactor-1
 * @param urgentChildSlots set of 0-based child slot indices on urgent paths through this node;
 *   empty means this node is not on any urgent path
 */
private[actors] final case class InteriorNode(
  firstChildId: NodeId,
  urgentChildSlots: Set[Int] = Set.empty
) {

  def childIds(childCount: Int): IndexedSeq[NodeId] =
    (0 until childCount).map(slot => firstChildId + slot)
}
