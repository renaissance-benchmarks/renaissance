package io.reactors
package container



import io.reactors.algebra.Abelian
import scala.collection._



/** Stores elements of an Abelian group.
 *
 *  Aggregation is computed incrementally using a binary operator
 *  and its inverse.
 */
class AbelianCatamorph[@spec(Int, Long, Double) T, @spec(Int, Long, Double) S](
  val get: S => T, val zero: T, val op: (T, T) => T, val inv: (T, T) => T
)(
  implicit val canT: Arrayable[T], val canS: Arrayable[S]
) extends RCatamorph[T, S] with RContainer.Modifiable {
  import AbelianCatamorph._

  private[reactors] var subscription: Subscription = _
  private[reactors] var elements: RFlatHashMap[S, T] = null
  private var insertsEmitter: Events.Emitter[S] = null
  private var removesEmitter: Events.Emitter[S] = null
  private var value: RCell[T] = null

  def inserts: Events[S] = insertsEmitter

  def removes: Events[S] = removesEmitter

  def init(z: T) {
    subscription = Subscription.empty
    elements = new RFlatHashMap[S, T]
    insertsEmitter = new Events.Emitter[S]
    removesEmitter = new Events.Emitter[S]
    value = RCell[T](zero)
  }

  init(zero)

  def unsubscribe() = subscription.unsubscribe()

  def signal = value

  def +=(v: S): Boolean = try {
    acquireModify()
    if (!elements.contains(v)) {
      val x = get(v)
      elements(v) = x
      value := op(value(), x)
      insertsEmitter.react(v, null)
      true
    } else false
  } finally releaseModify()

  def -=(v: S): Boolean = try {
    acquireModify()
    if (elements.contains(v)) {
      val y = elements(v)
      elements.remove(v)
      value := inv(value(), y)
      removesEmitter.react(v, null)
      true
    } else false
  } finally releaseModify()

  def container = this

  def push(v: S): Boolean = try {
    acquireModify()
    if (elements.contains(v)) {
      val y = elements(v)
      val x = get(v)
      elements(v) = x
      value := op(inv(value(), y), x)
      true
    } else false
  } finally releaseModify()

  def size = elements.size

  def foreach(f: S => Unit) = elements.foreachPair((k, v) => f(k))
}


object AbelianCatamorph {

  def apply[@spec(Int, Long, Double) T](implicit g: Abelian[T], can: Arrayable[T]) = {
    new AbelianCatamorph[T, T](v => v, g.zero, g.operator, g.inverse)
  }

  implicit def factory[@spec(Int, Long, Double) T: Abelian: Arrayable] = {
    val cm = implicitly[Abelian[T]]
    val a = implicitly[Arrayable[T]]
    new RContainer.Factory[T, AbelianCatamorph[T, T]] {
      def apply(inserts: Events[T], removes: Events[T]): AbelianCatamorph[T, T] = {
        val mc = AbelianCatamorph(cm, a)
        mc.subscription = new Subscription.Composite(
          inserts.onEvent(mc += _),
          removes.onEvent(mc -= _)
        )
        mc
      }
    }
  }

}
