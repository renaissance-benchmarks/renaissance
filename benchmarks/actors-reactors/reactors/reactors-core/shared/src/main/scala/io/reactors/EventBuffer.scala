package io.reactors



import io.reactors.common.UnrolledRing



/** An event buffer that is simultaneously an event stream.
 *
 *  Events are stored into the buffer with the `enqueue` method.
 *  Events are dequeued and simultaneously emitted with the `dequeue` method.
 *  Calling `unsubscribe` unreacts.
 *
 *  '''Note:''' this class can only be used inside a single reactor, and is not meant
 *  to be shared across multiple threads.
 *
 *  @tparam T       type of the events in this event stream
 */
class EventBuffer[@spec(Int, Long, Double) T: Arrayable]
extends Events.Push[T] with Events[T] with Subscription.Proxy {
  private[reactors] var buffer: UnrolledRing[T] = _
  private[reactors] var availabilityCell: RCell[Boolean] = _
  private[reactors] var rawSubscription: Subscription = _

  private[reactors] def init(self: EventBuffer[T]) {
    buffer = new UnrolledRing[T]
    availabilityCell = new RCell[Boolean](false)
    rawSubscription = Subscription.empty
  }

  init(this)

  private[reactors] def subscription_=(s: Subscription) = {
    rawSubscription = new Subscription.Composite(
      s,
      new Subscription {
        override def unsubscribe(): Unit = unreactAll()
      }
    )
  }

  /** The subscription associated with this event buffer.
   */
  def subscription: Subscription = rawSubscription

  /** Enqueues an event.
   */
  def enqueue(x: T): Unit = {
    try buffer.enqueue(x)
    finally {
      if (!availabilityCell()) availabilityCell := true
    }
  }

  /** Dequeues a previously enqueued event.
   *
   *  The event stream is first published on the associated event stream, then returned.
   */
  def dequeue(): T = {
    val x = buffer.dequeue()
    try reactAll(x, null)
    finally if (buffer.isEmpty) {
      if (availabilityCell()) availabilityCell := false
    }
    x
  }

  /** A signal that designates whether the event buffer has events to dequeue.
   */
  def available: Signal[Boolean] = availabilityCell

  /** Size of the event buffer.
   */
  def size: Int = buffer.size

  /** Returns `true` iff the buffer is empty.
   */
  def isEmpty: Boolean = buffer.isEmpty

  /** Returns `true` iff the buffer is non-empty.
   */
  def nonEmpty: Boolean = buffer.nonEmpty
}
