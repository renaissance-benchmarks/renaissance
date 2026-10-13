package org.renaissance.actors

import akka.actor.ActorRef
import akka.dispatch.ControlMessage

/**
 * Sealed marker trait for all benchmark messages; allows distinguishing them from Akka-internal
 * ones in [[akka.actor.DeadLetter]] and [[akka.actor.UnhandledMessage]] events.
 */
private[actors] sealed trait UctMessage

// -------------------------------------------------------------------------
//  Build protocol
// -------------------------------------------------------------------------

/** Sent to the root to kick off tree construction. */
private[actors] case object GenerateTreeMessage extends UctMessage

/** Sent to a newly spawned node, triggering it to query its parent for expansion info. */
private[actors] case object CheckExpansionMessage extends UctMessage

/** Sent by a node to its parent to ask whether it should expand. */
private[actors] final case class ExpansionQueryMessage(sender: ActorRef, senderId: NodeId)
  extends UctMessage

/**
 * Parent's reply to an [[ExpansionQueryMessage]]: the node is interior; it should create
 * children starting at [[firstChildId]]. [[urgentChildSlots]] identifies which 0-based
 * child slots lie on urgent paths; empty when no urgent paths pass through this node.
 */
private[actors] final case class CreateChildrenMessage(
  firstChildId: NodeId,
  urgentChildSlots: Set[Int] = Set.empty
) extends UctMessage

/** Parent's reply to an [[ExpansionQueryMessage]]: the node is a leaf; no children to create. */
private[actors] case object StayLeafMessage extends UctMessage

/**
 * Sent bottom-up after a subtree is fully built: leaves send it upon [[StayLeafMessage]];
 * interior nodes send it once all children have reported.
 */
private[actors] case object SubtreeCreatedMessage extends UctMessage

// -------------------------------------------------------------------------
//  Collection protocol
// -------------------------------------------------------------------------

/**
 * Sent top-down from a parent to each of its children to request a temperature reading;
 * each child replies with a [[TemperatureReadingMessage]].
 */
private[actors] case object MeasureTemperatureMessage extends UctMessage

/** Carries a temperature reading from a child back to its parent. */
private[actors] final case class TemperatureReadingMessage(temperature: Double)
  extends UctMessage

/**
 * Injected into urgent children during the shock reduction. Extends [[ControlMessage]] so
 * the priority mailbox delivers it before any queued [[MeasureTemperatureMessage]],
 * ensuring urgent leaves report their updated temperature within the same reduction.
 */
private[actors] final case class UrgentUpdateTemperatureMessage(temperature: Double)
  extends UctMessage
  with ControlMessage

// -------------------------------------------------------------------------
//  Teardown protocol
// -------------------------------------------------------------------------

/** Sent top-down to initiate teardown; interior nodes cascade it to their children before stopping. */
private[actors] case object TerminateMessage extends UctMessage

/**
 * Sent bottom-up after a subtree is fully dismantled, symmetric to [[SubtreeCreatedMessage]]:
 * leaves send it upon [[TerminateMessage]]; interior nodes send it once all children report.
 */
private[actors] case object SubtreeDestroyedMessage extends UctMessage
