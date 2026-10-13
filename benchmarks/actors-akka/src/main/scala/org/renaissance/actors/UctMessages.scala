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
 * Request to create a subtree. The recipient looks up its expansion in the topology: a
 * leaf reports right away, and an interior node creates its children and passes the
 * request on to them.
 */
private[actors] case object CreateSubtreeMessage extends UctMessage

/**
 * Report that a subtree is fully built. A leaf sends it to its parent upon
 * [[CreateSubtreeMessage]], and an interior node once all of its children have reported.
 */
private[actors] case object SubtreeCreatedMessage extends UctMessage

// -------------------------------------------------------------------------
// Measurement collection protocol
// -------------------------------------------------------------------------

/**
 * Request for a temperature reading. A parent sends it to each of its children, and each
 * child replies with a [[TemperatureReadingMessage]].
 */
private[actors] case object MeasureTemperatureMessage extends UctMessage

/** A temperature reading, sent by a child to its parent. */
private[actors] final case class TemperatureReadingMessage(temperature: Double)
  extends UctMessage

/**
 * Update of the temperature of the urgent leaves, sent down the urgent paths right after
 * a measurement request. Extends [[ControlMessage]], so the priority mailbox delivers it
 * before a [[MeasureTemperatureMessage]] still waiting in the same mailbox, and the waiting
 * measurement observes the updated temperature.
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

private[actors] final case class LocalCreateUctMessage(done: Promise[Unit]) extends UctMessage

private[actors] final case class LocalMeasureTemperatureMessage(result: Promise[Double])
  extends UctMessage

private[actors] final case class LocalMeasureTemperatureWithUrgentUpdateMessage(
  temperature: Double,
  result: Promise[Double]
) extends UctMessage

private[actors] final case class LocalDestroyUctMessage(done: Promise[Unit]) extends UctMessage
