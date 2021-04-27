package io.reactors



import scala.collection._



/** An event stream that can be either completed, or unreacted at most once.
 *
 *  Assigning a value propagates an event to all the subscribers,
 *  and then propagates an unreaction.
 *  To assign a value:
 *
 *  {{{
 *  val iv = new Events.IVar[Int]
 *  iv := 5
 *  assert(iv() == 5)
 *  }}}
 *
 *  To unreact (i.e. seal, or close) an ivar without assigning a value:
 *
 *  {{{
 *  val iv = new Events.IVar[Int]
 *  iv.unreact()
 *  assert(iv.isUnreacted)
 *  }}}
 *  
 *  @tparam T          type of the value in the `IVar`
 */
class IVar[@spec(Int, Long, Double) T] extends Signal[T] {
  private var state = 0
  private var exception: Throwable = _
  private var value: T = _
  private var pushSource: Events.PushSource[T] = _

  private[reactors] def init(dummy: IVar[T]) {
    pushSource = new Events.PushSource[T]
  }

  init(this)

  /** Returns `true` iff the ivar has been completed, i.e. assigned or failed.
   */
  def isCompleted: Boolean = state != 0

  /** Returns `true` iff the ivar has been assigned.
   */
  def isAssigned: Boolean = state == 1

  /** Returns `true` iff the ivar has been failed with an exception.
   */
  def isFailed: Boolean = state == -1

  /** Returns `true` iff the ivar is unassigned.
   */
  def isUnassigned: Boolean = state == 0

  /** Returns the value of the ivar if it was failed already assigned,
   *  and throws an exception otherwise.
   */
  def apply(): T = {
    if (state == 1) value
    else if (state == -1) throw exception
    else sys.error("IVar unassigned.")
  }

  def unsubscribe() = tryUnreact()

  /** Returns true if this ivar is unassigned or failed.
   */
  def isEmpty = isUnassigned || isFailed

  /** Returns the exception in the ivar if it was failed.
   *
   *  Throws an exception otherwise.
   */
  def failure: Throwable = {
    if (state == -1) exception
    else sys.error("IVar not failed.")
  }

  def onReaction(obs: Observer[T]): Subscription = {
    if (isFailed) {
      obs.except(failure)
      obs.unreact()
      Subscription.empty
    } else if (isAssigned) {
      obs.react(this(), null)
      obs.unreact()
      Subscription.empty
    } else {
      pushSource.onReaction(obs)
    }
  }

  /** Assigns a value to the ivar if it is unassigned,
   *
   *  Throws an exception otherwise.
   */
  def :=(x: T): Unit = if (state == 0) {
    state = 1
    value = x
    pushSource.reactAll(x, null)
    pushSource.unreactAll()
  } else sys.error("IVar is already assigned.")

  def react(x: T) = this := x

  /** Attempts to complete the `IVar` if not already completed.
   */
  def tryReact(x: T): Boolean = if (state == 0) {
    react(x)
    true
  } else false

  /** Fails the `IVar` unless already completed, in which case it throws.
   */
  def except(t: Throwable) = if (!tryExcept(t)) sys.error("IVar is already completed.")

  /** Attempts to fail the `IVar` unless already completed.
   */
  def tryExcept(t: Throwable): Boolean = if (state == 0) {
    state = -1
    exception = t
    pushSource.exceptAll(exception)
    pushSource.unreactAll()
    true
  } else false

  /** Fails the ivar with the `NoSuchElementException` if it is unassigned.
   *
   *  If completed, throws an exception.
   */
  def unreact(): Unit = tryUnreact() || sys.error("IVar is already completed.")

  /** Tries to fail the ivar with the `NoSuchElementException`.
   *
   *  Returns `false` if the ivar is completed.
   */
  def tryUnreact(): Boolean = tryExcept(new NoSuchElementException)

}


object IVar {
  /** Creates an `IVar` that is already completed.
   */
  def apply[@spec(Int, Long, Double) T](x: T): IVar[T] = {
    val iv = new IVar[T]
    iv := x
    iv
  }

  /** Creates an `IVar` that is completed with a `NoSuchElementException`.
   */
  def empty[@spec(Int, Long, Double) T]: IVar[T] = {
    val iv = new IVar[T]
    iv.unreact()
    iv
  }
}
