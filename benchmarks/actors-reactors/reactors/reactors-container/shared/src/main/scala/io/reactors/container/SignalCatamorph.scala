package io.reactors
package container



import io.reactors.algebra._
import scala.collection._



/** Catamorph of signal values.
 *
 *  Aggregates a bunch of signals using a regular catamorph.
 *  A regular catamorph aggregates a set of values of one type,
 *  and exposes a signal that is their aggregation.
 *  A signal catamorph aggregates a set of signals of some type,
 *  and exposes a signal that is the aggregation of the signals
 *  it contains. The difference is that when any of the signal
 *  values changes, the output signal also changes. This is
 *  not the case with a regular catamorph, which only updates
 *  itself when a value is inserted or removed.
 *
 *  Example:
 *
 *  {{{
 *  Signal(1)--|
 *             +--Signal(3)
 *  Signal(2)--|
 *  
 *  -- after change --
 *  
 *  Signal(3)--|
 *             +--Signal(5) -> updated!
 *  Signal(2)--|
 *  }}}
 *
 *  @tparam T          type of values inside the signals
 *  @param catamorph   regular catamorph of the signals
 */
class SignalCatamorph[@spec(Int, Long, Double) T](
  val catamorph: RCatamorph[T, Signal[T]]
) extends RCatamorph[T, Signal[T]] {
  private[reactors] var subscription: Subscription = _
  private var signalSubscriptions = mutable.Map[Signal[T], Subscription]()
  private var insertsEvents: Events[Signal[T]] = null
  private var removesEvents: Events[Signal[T]] = null
  private var defaultSignal: Signal[T] with Events.Push[T] = null

  def init(c: RCatamorph[T, Signal[T]]) {
    subscription = Subscription.empty
    insertsEvents = catamorph.inserts
    removesEvents = catamorph.removes
    defaultSignal = new Signal[T] with Events.Push[T] {
      def apply() = catamorph.signal()
      def isEmpty = catamorph.signal.isEmpty
      def unsubscribe() {}
    }
  }

  init(catamorph)

  def unsubscribe() = subscription.unsubscribe()

  def signal: Signal[T] = defaultSignal
  
  def +=(s: Signal[T]): Boolean = {
    if (catamorph += s) {
      signalSubscriptions(s) = s.onReaction(new Observer[T] {
        def react(v: T, hint: Any) {
          catamorph.push(s)
          defaultSignal.reactAll(catamorph.signal(), null)
        }
        def except(t: Throwable) {
          defaultSignal.exceptAll(t)
        }
        def unreact() {}
      })
      defaultSignal.reactAll(catamorph.signal(), null)
      true
    } else false
  }

  def -=(s: Signal[T]): Boolean = {
    if (catamorph -= s) {
      signalSubscriptions(s).unsubscribe()
      signalSubscriptions.remove(s)
      defaultSignal.reactAll(catamorph.signal(), null)
      true
    } else false
  }

  def push(s: Signal[T]) = catamorph.push(s)

  def inserts: Events[Signal[T]] = insertsEvents

  def removes: Events[Signal[T]] = removesEvents

  def size = signalSubscriptions.size

  def foreach(f: Signal[T] => Unit) = signalSubscriptions.keys.foreach(f)

  override def toString = s"SignalCatamorph(${signal()})"
}


trait LowLowSignalCatamorph {
  implicit def monoidFactory[@spec(Int, Long, Double) T](implicit m: Monoid[T]) = {
    new RContainer.Factory[Signal[T], SignalCatamorph[T]] {
      def apply(inserts: Events[Signal[T]], removes: Events[Signal[T]]):
        SignalCatamorph[T] = {
        val mc = new SignalCatamorph[T](SignalCatamorph.monoid(m))
        mc.subscription = new Subscription.Composite(
          inserts.onEvent(mc += _),
          removes.onEvent(mc -= _)
        )
        mc
      }
    }
  }
}


trait LowSignalCatamorph extends LowLowSignalCatamorph {
  implicit def commuteFactory[@spec(Int, Long, Double) T](implicit cm: Commute[T]) = {
    new RContainer.Factory[Signal[T], SignalCatamorph[T]] {
      def apply(inserts: Events[Signal[T]], removes: Events[Signal[T]]):
        SignalCatamorph[T] = {
        val mc = new SignalCatamorph[T](SignalCatamorph.commute(cm))
        mc.subscription = new Subscription.Composite(
          inserts.onEvent(mc += _),
          removes.onEvent(mc -= _)
        )
        mc
      }
    }
  }
}


object SignalCatamorph extends LowSignalCatamorph {

  def monoid[@spec(Int, Long, Double) T](implicit m: Monoid[T]) = {
    val catamorph = new MonoidCatamorph[T, Signal[T]](_(), m.zero, m.operator)
    new SignalCatamorph[T](catamorph)
  }

  def commute[@spec(Int, Long, Double) T](implicit cm: Commute[T]) = {
    val catamorph = new CommuteCatamorph[T, Signal[T]](_(), cm.zero, cm.operator)
    new SignalCatamorph[T](catamorph)
  }

  def abelian[@spec(Int, Long, Double) T](implicit m: Abelian[T], a: Arrayable[T]) = {
    val catamorph =
      new AbelianCatamorph[T, Signal[T]](_(), m.zero, m.operator, m.inverse)
    new SignalCatamorph[T](catamorph)
  }

  def apply[@spec(Int, Long, Double) T](m: Monoid[T]) = monoid(m)

  def apply[@spec(Int, Long, Double) T](cm: Commute[T]) = commute(cm)

  def apply[@spec(Int, Long, Double) T](cm: Abelian[T])(implicit a: Arrayable[T]) =
    abelian(cm, a)

  implicit def abelianFactory[@spec(Int, Long, Double) T](
    implicit cm: Abelian[T], a: Arrayable[T]
  ) = {
    new RContainer.Factory[Signal[T], SignalCatamorph[T]] {
      def apply(inserts: Events[Signal[T]], removes: Events[Signal[T]]):
        SignalCatamorph[T] = {
        val mc = new SignalCatamorph[T](SignalCatamorph.abelian(cm, a))
        mc.subscription = new Subscription.Composite(
          inserts.onEvent(mc += _),
          removes.onEvent(mc -= _)
        )
        mc
      }
    }
  }

}
