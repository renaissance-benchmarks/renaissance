package org.renaissance.actors

import akka.dispatch.ControlMessage

import scala.concurrent.Promise

/**
 * Sealed marker trait for all benchmark messages.
 * Makes them distinct from Akka-internal messages.
 */
private[actors] sealed trait UctMessage

// -------------------------------------------------------------------------
// Tree construction protocol
// -------------------------------------------------------------------------

/**
 * Request to create a subtree. The recipient node looks up its expansion in the
 * plan: a leaf responds right away, while an interior node creates its children
 * and passes the request on to them.
 */
private[actors] case object CreateSubtreeMessage extends UctMessage

/**
 * A leaf and its distance (number of edges) from some (implicit) reference node.
 * The reference node is known in the context in which the record is used, so the
 * instances may represent the distance from root or other interior nodes.
 *
 * @param leafId leaf node ID
 * @param distance distance of the leaf from the reference node
 */
private[actors] final case class LeafDistance(leafId: NodeId, distance: Int) {

  /** The same leaf, the given number of edges farther away. */
  def fartherBy(edgeCount: Int): LeafDistance = LeafDistance(leafId, distance + edgeCount)
}

private[actors] object LeafDistance {

  /** Orders leaves by highest distance (farthest) and lowest ID first. */
  given farthestFirst: Ordering[LeafDistance] = Ordering.by { leaf =>
    (-leaf.distance, leaf.leafId)
  }

  /** The entry with the farthest distance as ordered by [[farthestFirst]]. */
  def farthestOf[K](leafDistances: collection.Map[K, LeafDistance]): (K, LeafDistance) =
    leafDistances.minBy((_, leafDistance) => leafDistance)
}

/**
 * A tree checksum built of the number of nodes in the tree and the sum of their IDs.
 * Allows detecting a missing, extra, or misnumbered node in the UCT built by the actors.
 * Does not tie children to their parents, because each node creates the children given
 * by its own expansion in the plan, and the structure of the tree thus follows from the
 * node IDs. Compared to the topology checksum (see [[AkkaUct.treeChecksum]]).
 */
private[actors] final case class TreeChecksum(nodeCount: Int, nodeIdSum: Long) {

  /** The checksum combined with the checksum of a tree (that shares no node with it). */
  def combinedWith(other: TreeChecksum): TreeChecksum =
    TreeChecksum(nodeCount + other.nodeCount, nodeIdSum + other.nodeIdSum)
}

private[actors] object TreeChecksum {

  /** The checksum of a single-node tree. */
  def of(nodeId: NodeId): TreeChecksum = TreeChecksum(nodeCount = 1, nodeId.toLong)
}

/**
 * Report that a subtree is fully built, with the checksum of the subtree and the leaf
 * farthest from its root. A leaf sends it to its parent upon [[CreateSubtreeMessage]],
 * while an interior node sends it when all of its children have reported.
 */
private[actors] final case class SubtreeCreatedMessage(
  checksum: TreeChecksum,
  farthestLeaf: LeafDistance
) extends UctMessage

// -------------------------------------------------------------------------
// Urgent path selection protocol
// -------------------------------------------------------------------------

/**
 * Request for offers of the next urgent paths, which branch off the selected ones at the
 * nodes `branchDistance` levels below the recipient. The request travels down the urgent
 * paths selected so far. When `branchDistance` is zero, the recipient offers, for each
 * child that is not on an urgent path, the leaf farthest from that child, if the distance
 * of the leaf from the recipient is `leafDistanceMin` or more. The recipient replies with
 * an [[UrgentPathOffersMessage]].
 */
private[actors] final case class CollectUrgentPathOffersMessage(
  branchDistance: Int,
  leafDistanceMin: Int,
  offerCountMax: Int
) extends UctMessage

/**
 * Offers of the leaves that would end the next urgent paths, collected in a subtree and
 * sent to the parent of its root: at most `offerCountMax` of them, in the order of
 * preference. The distance of each offered leaf is counted from the node that offered it.
 * All offers of a round come from nodes at the same depth, so their distances compare in
 * the same way as the depths of the offered leaves.
 */
private[actors] final case class UrgentPathOffersMessage(offers: Seq[LeafDistance])
  extends UctMessage

/**
 * Selection of the urgent paths ending in the given leaves. It travels down the tree, and
 * each node records the children through which the paths continue as urgent and passes
 * the leaves on to them.
 */
private[actors] final case class SelectUrgentPathsMessage(leafIds: Seq[NodeId])
  extends UctMessage

/**
 * Report that the urgent paths of a [[SelectUrgentPathsMessage]] are recorded in a subtree.
 * A leaf sends it to its parent right away, and an interior node once all children it
 * passed leaves to have reported.
 */
private[actors] case object UrgentPathsSelectedMessage extends UctMessage

// -------------------------------------------------------------------------
// Measurement collection protocol
// -------------------------------------------------------------------------

/**
 * Identifies a temperature measurement. Allows keeping track of measurements
 * in progress, assigned in the order in which the measurements are requested.
 * As an opaque type, the identifier cannot be mixed up with other integers.
 */
opaque private[actors] type MeasurementId = Int

private[actors] object MeasurementId {

  /** The ID of the first measurement. */
  val First: MeasurementId = 0

  extension (id: MeasurementId) {

    /** The ID of the measurement requested after this one. */
    def next: MeasurementId = id + 1
  }
}

/**
 * Request for a temperature reading for the given measurement. A parent sends it to each
 * of its children, and each child replies with a [[TemperatureReadingMessage]] for the
 * same measurement. Several measurements may be in progress at the same time.
 */
private[actors] final case class MeasureTemperatureMessage(measurementId: MeasurementId)
  extends UctMessage

/** A temperature reading for the given measurement, sent by a child to its parent. */
private[actors] final case class TemperatureReadingMessage(
  measurementId: MeasurementId,
  temperature: Double
) extends UctMessage

/**
 * Update of the temperature of the urgent leaves, sent down the urgent paths after
 * the measurement requests. Extends [[ControlMessage]], so the priority mailbox
 * delivers it before any [[MeasureTemperatureMessage]] still waiting in the same
 * mailbox, causing the waiting measurements to observe the updated temperature.
 */
private[actors] final case class UrgentUpdateTemperatureMessage(temperature: Double)
  extends UctMessage
  with ControlMessage

// -------------------------------------------------------------------------
// Teardown protocol
// -------------------------------------------------------------------------

/**
 * Request to tear down a subtree. A leaf stops immediately, an interior node
 * passes the request on to its children and stops once they have all responded.
 */
private[actors] case object DestroySubtreeMessage extends UctMessage

/**
 * Report that a subtree is fully torn down, the counterpart of [[SubtreeCreatedMessage]].
 * A leaf sends it to its parent upon [[DestroySubtreeMessage]], an interior node sends
 * it once all of its children have reported.
 */
private[actors] case object SubtreeDestroyedMessage extends UctMessage

// -------------------------------------------------------------------------
// Orchestration protocol
// -------------------------------------------------------------------------

// Messages sent by the benchmark thread to the UctCoordinatorActor.
// Local use only, because most messages contain a Promise.

private[actors] final case class LocalCreateUctMessage(result: Promise[TreeChecksum])
  extends UctMessage

private[actors] final case class LocalSelectUrgentPathsMessage(
  pathCount: Int,
  pathLengthFractionMin: Double,
  result: Promise[Seq[NodeId]]
) extends UctMessage

private[actors] final case class LocalMeasureTemperatureMessage(result: Promise[Double])
  extends UctMessage

private[actors] final case class LocalUrgentUpdateTemperatureMessage(temperature: Double)
  extends UctMessage

private[actors] final case class LocalDestroyUctMessage(done: Promise[Unit]) extends UctMessage

// -------------------------------------------------------------------------
// Collection protocol
// -------------------------------------------------------------------------

// Local-only messages sent by the benchmark thread to the UctCollectorActor.

private[actors] final case class LocalTakeCollectedMessagesMessage(
  result: Promise[Seq[UctMessage]]
) extends UctMessage
