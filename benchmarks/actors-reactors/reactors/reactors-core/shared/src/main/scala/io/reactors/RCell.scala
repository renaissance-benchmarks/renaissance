package io.reactors



import scala.reflect.ClassTag



/** The reactive cell abstraction represents a mutable memory location
 *  whose changes may produce events.
 *
 *  An `RCell` is conceptually similar to a reactive emitter lifted into a signal.
 *  An `RCell` can be created full, or empty. If empty, retrieving its value throws
 *  an exception. Once assigned, the `RCell` is no longer empty, until `clear` gets
 *  called.
 *
 *  @tparam T         the type of the values it stores
 *  @param value      the initial value of the reactive cell
 */
class RCell[@spec(Int, Long, Double) T] private[reactors] (
  private[reactors] var value: T,
  private[reactors] var hasValue: Boolean,
  private[reactors] var subscription: Subscription
) extends Signal[T] with Observer[T] {
  private var pushSource: Events.PushSource[T] = _

  private[reactors] def init(dummy: RCell[T]) {
    pushSource = new Events.PushSource[T]
  }

  init(this)

  /** Creates an empty `RCell`
   */
  def this() = this(null.asInstanceOf[T], false, Subscription.empty)

  /** Creates an `RCell`, initialized with a value.
   */
  def this(v: T) = this(v, true, Subscription.empty)

  /** Returns the current value in the reactive cell.
   */
  def apply(): T = {
    if (!hasValue) throw new NoSuchElementException("<empty>.apply()")
    value
  }

  /** Returns `false`. */
  def isEmpty = !hasValue

  /** If this `RCell` is bound to an event source, this unsubscribes from it. */
  def unsubscribe() = subscription.unsubscribe()

  /** Assigns a new value to the reactive cell,
   *  and emits an event with the new value to all the subscribers.
   *
   *  @param v        the new value
   */
  def :=(v: T): Unit = {
    value = v
    hasValue = true
    pushSource.reactAll(v, null)
  }

  /** Clears the content of this reactive cell, making it empty.
   */
  def clear(): Unit = {
    value = null.asInstanceOf[T]
    hasValue = false
  }

  /** Same as `:=`. */
  def react(x: T) = this := x

  def react(x: T, hint: Any) = react(x)

  /** Propagates the exception to all the reactors.
   */
  def except(t: Throwable) = pushSource.exceptAll(t)

  /** Does nothing -- a cell never unreacts.
   */
  def unreact() {}

  def onReaction(obs: Observer[T]): Subscription = {
    if (hasValue) obs.react(value, null)
    pushSource.onReaction(obs)
  }

  override def toString = s"RCell($value)"

}


object RCell {

  /** A factory method for creating reactive cells.
   */
  def apply[@spec(Int, Long, Double) T](x: T): RCell[T] = new RCell[T](x)

  /** Creates an empty reactive cell.
   */
  def apply[@spec(Int, Long, Double) T]: RCell[T] = new RCell[T]()

}
