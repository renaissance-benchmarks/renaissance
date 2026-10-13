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

private[actors] final case class LocalCreateUctMessage(done: Promise[Unit]) extends UctMessage

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
