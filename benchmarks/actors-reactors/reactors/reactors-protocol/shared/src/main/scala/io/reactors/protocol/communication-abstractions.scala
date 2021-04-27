package io.reactors
package protocol






trait CommunicationAbstractions {
  trait Connection[T] {
    def events: Events[T]
    def subscription: Subscription
  }

  trait ServerSide[R, C] {
    def channel: Channel[R]
    def links: Events[C]
    def subscription: Subscription
  }

  case class Valve[T](
    channel: Channel[T],
    available: Signal[Boolean],
    subscription: Subscription
  )

  case class Pump[T](
    buffer: EventBuffer[T],
    subscription: Subscription
  ) {
    def available: Signal[Boolean] = buffer.available

    def events: Events[T] = buffer.events

    def dequeue(): T = buffer.dequeue()
  }
}
