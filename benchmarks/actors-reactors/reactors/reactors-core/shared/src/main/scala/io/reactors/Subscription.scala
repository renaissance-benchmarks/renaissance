package io.reactors



import scala.collection._



/** A subscription to a certain kind of event, event processing or computation.
 *
 *  Calling `unsubscribe` on the subscription causes the events to no longer be
 *  propagated to this subscription, or some computation to cease.
 *
 *  Unsubscribing is idempotent -- calling `unsubscribe` second time does nothing.
 */
trait Subscription {
  self =>

  /** Stops event propagation on the corresponding event stream.
   */
  def unsubscribe(): Unit

  /** Returns a new subscription that unsubscribes this, and then executes an action.
   */
  def andThen(action: =>Unit): Subscription = new Subscription {
    def unsubscribe() {
      self.unsubscribe()
      action
    }
  }

  /** Returns a new subscription that unsubscribes this subscription, and then another.
   */
  def chain(other: Subscription): Subscription = new Subscription {
    def unsubscribe() {
      self.unsubscribe()
      other.unsubscribe()
    }
  }
}


/** Default subscription implementations.
 */
object Subscription {
  /** Returns a subscription that runs the specified action when unsubscribed.
   *
   *  The action **will not be** executed more than once.
   */
  def apply[U](action: =>U) = new Subscription {
    var unsubscribed = false
    def unsubscribe() = if (!unsubscribed) {
      unsubscribed = true
      action
    }
  }

  /** Does not unsubscribe from anything. */
  val empty = new Subscription {
    def unsubscribe() = {}
  }

  /** Subscription composed of several subscriptions.
   *
   *  When unsubscribed, all the component subscriptions get unsubscribed.
   */
  class Composite(ss: Subscription*) extends Subscription {
    def unsubscribe() {
      for (s <- ss) s.unsubscribe()
    }
  }

  /** Forwards `unsubscribe` to another subscription.
   */
  trait Proxy extends Subscription {
    def subscription: Subscription
    def unsubscribe() {
      subscription.unsubscribe()
    }
  }

  /** A mutable collection of subscriptions, which is itself a subscription.
   *
   *  When unsubscribed from, all containing subscriptions are unsubscribed.
   *  Subsequently added subscriptions are automatically unsubscribed.
   */
  class Collection extends Subscription {
    private var done = false
    private val set = mutable.Set[Subscription]()
    def unsubscribe() {
      done = true
      for (s <- set.toArray) s.unsubscribe()
    }
    def addAndGet(s: Subscription): Subscription = {
      if (done) {
        s.unsubscribe()
        Subscription.empty
      } else {
        val ns = new Subscription {
          override def unsubscribe() {
            s.unsubscribe()
            set -= this
          }
        }
        set += ns
        ns
      }
    }
    def remove(s: Subscription): Boolean = set.remove(s)
    def isEmpty: Boolean = set.isEmpty
  }

  /** A mutable cell that can contain at most one subscription.
   *
   *  Has similar semantics as subscription collection.
   */
  class Cell extends Subscription {
    private var done = false
    private var inner: Subscription = null
    def unsubscribe() {
      done = true
      if (inner != null) inner.unsubscribe()
    }
    def set(s: Subscription): Subscription = {
      if (done) {
        s.unsubscribe()
        Subscription.empty
      } else {
        inner = new Subscription {
          override def unsubscribe() {
            s.unsubscribe()
            inner = null
          }
        }
        inner
      }
    }
  }

}
