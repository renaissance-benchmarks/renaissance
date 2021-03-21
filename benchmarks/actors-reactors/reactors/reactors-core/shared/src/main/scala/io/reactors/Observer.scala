package io.reactors






/** An object that can act upon an event or be signalled that
 *  there will be no more events.
 *
 *  @tparam T        type of events the observer responds to
 */
trait Observer[@spec(Int, Long, Double) T] {

  /** Called by an event stream when an event `value` is produced.
   *
   *  @param value   the event passed to the observer
   *  @param hint    an additional, optional value from the event source, usually `null`
   */
  def react(value: T, hint: Any): Unit

  /** Called by an event stream when an exception is produced.
   *
   *  @param t       the exception passed to the observer
   */
  def except(t: Throwable): Unit

  /** Called by an event stream when there will be no further updates.
   */
  def unreact(): Unit

}


object Observer {
  /** Creates an observer using the specified handlers.
   */
  def apply[@spec(Int, Long, Double) T](
    eh: T => Unit, th: Throwable => Unit, uh: () => Unit
  ): Observer[T] = {
    new Observer[T] {
      def react(value: T, hint: Any) = eh(value)
      def except(t: Throwable) = th(t)
      def unreact() = uh()
    }
  }
}
