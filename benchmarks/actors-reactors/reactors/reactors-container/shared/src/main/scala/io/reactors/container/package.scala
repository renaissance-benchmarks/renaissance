package io.reactors






package object container {
  import scala.language.implicitConversions

  implicit def events2ops[@spec(Int, Long, Double) T](self: Events[T]): EventsOps[T] =
    new EventsOps(self)

  class EventsOps[@spec(Int, Long, Double) T](val self: Events[T]) {

    /** Accumulates all the events from this event stream into a new container of the
     *  specified type.
     *
     *  The events are added to the specified container until this event stream
     *  unreacts.
     *  It is the client's responsibility to ensure that the event stream is not
     *  unbounded.
     *
     *  @tparam That     the type of the reactive container
     *  @param factory   the factory of the builder objects for the specified container
     *  @result          the reactive container with all the emitted events
     */
    def to[That <: RContainer[T]](
      implicit factory: RContainer.Factory[T, That]
    ): That = {
      factory(self, new Events.Never)
    }

  }

}
