package io.reactors
package container



import io.reactors.algebra._
import scala.collection._



/** Stores elements of a monoid.
 *
 *  Incrementally computes an aggregation of the stored elements,
 *  using a binary associative operator. The aggregation can be accessed
 *  with the `signal` method.
 */
class MonoidCatamorph[@spec(Int, Long, Double) T, @spec(Int, Long, Double) S](
  val get: S => T, val zero: T, val op: (T, T) => T
) extends RCatamorph[T, S] with RContainer.Modifiable {
  import MonoidCatamorph._

  private[reactors] var subscription: Subscription = _
  private[reactors] var root: Node[T] = null
  private[reactors] var leaves: mutable.Map[S, Leaf[T]] = null
  private val insertsEmitter = new Events.Emitter[S]
  private val removesEmitter = new Events.Emitter[S]
  private var rootValue: RCell[T] = null

  def inserts: Events[S] = insertsEmitter

  def removes: Events[S] = removesEmitter

  def init(mc: MonoidCatamorph[T, S]) {
    root = new Empty(zero)
    leaves = mutable.Map[S, Leaf[T]]()
    rootValue = RCell(root.value)
    subscription = Subscription.empty
  }

  init(this)

  def signal: Signal[T] = rootValue

  protected def newLeaf(v: S, f: S => T) = new Leaf[T](() => f(v), null)

  def unsubscribe() = subscription.unsubscribe()

  def +=(v: S): Boolean = try {
    acquireModify()
    if (!leaves.contains(v)) {
      val leaf = newLeaf(v, get)
      leaves(v) = leaf
      root = root.insert(leaf, op)
      rootValue := root.value
      insertsEmitter.react(v, null)
      true
    } else false
  } finally releaseModify()

  def -=(v: S): Boolean = try {
    acquireModify()
    if (leaves.contains(v)) {
      val leaf = leaves(v)
      root = leaf.remove(zero, op)
      leaves.remove(v)
      rootValue := root.value
      removesEmitter.react(v, null)
      true
    } else false
  } finally releaseModify()

  def container = this

  def push(v: S): Boolean = try {
    acquireModify()
    if (leaves.contains(v)) {
      val leaf = leaves(v)
      leaf.pushUp(op)
      rootValue := root.value
      true
    } else false
  } finally releaseModify()

  def size = leaves.size

  def foreach(f: S => Unit) = leaves.keys.foreach(f)

}


object MonoidCatamorph {

  def apply[@spec(Int, Long, Double) T](implicit m: Monoid[T]) =
    new MonoidCatamorph[T, T](v => v, m.zero, m.operator)

  implicit def factory[@spec(Int, Long, Double) T: Monoid] =
    new RContainer.Factory[T, MonoidCatamorph[T, T]] {
      def apply(inserts: Events[T], removes: Events[T]): MonoidCatamorph[T, T] = {
        val m = implicitly[Monoid[T]]
        val mc = new MonoidCatamorph[T, T](v => v, m.zero, m.operator)
        mc.subscription = new Subscription.Composite(
          inserts.onEvent(mc += _),
          removes.onEvent(mc -= _)
        )
        mc
      }
    }

  sealed trait Node[@spec(Int, Long, Double) T] {
    def height: Int
    def value: T
    def parent: Inner[T]
    def parent_=(p: Inner[T]): Unit
    def pushUp(op: (T, T) => T): Unit
    def insert(leaf: Leaf[T], op: (T, T) => T): Node[T]
    def toString(indent: Int): String
    def housekeep(op: (T, T) => T) {}
    def asInner = this.asInstanceOf[Inner[T]]
    override def toString = toString(0)
    def localString: String
  }

  class Inner[@spec(Int, Long, Double) T](
    var height: Int, var left: Node[T], var right: Node[T], var parent: Inner[T]
  ) extends Node[T] {
    private var v: T = _
    def value: T = v
    def value_=(v: T) = this.v = v
    def pushUp(op: (T, T) => T) {
      v = op(left.value, right.value)
      if (parent != null) parent.pushUp(op)
    }
    private def balance = left.height - right.height
    private def heightOf(l: Node[T], r: Node[T]) = 1 + math.max(l.height, r.height)
    override def housekeep(op: (T, T) => T) {
      height = heightOf(left, right)
      value = op(left.value, right.value)
    }
    def insert(leaf: Leaf[T], op: (T, T) => T): Node[T] = {
      right = right.insert(leaf, op)
      right.parent = this
      housekeep(op)
      rebalance(op)
    }
    def rebalance(op: (T, T) => T): Node[T] = {
      val b = balance
      if (b < -1) {
        if (right.asInner.balance > 0) {
          right = right.asInner.rotr(op)
          right.parent = this
        }
        rotl(op)
      } else if (b > 1) {
        if (left.asInner.balance < 0) {
          left = left.asInner.rotl(op)
          left.parent = this
        }
        rotr(op)
      } else this
    }
    def rotl(op: (T, T) => T): Inner[T] = {
      val ntop = this.right.asInner
      this.right = ntop.left
      this.right.parent = this
      ntop.left = this
      this.parent = ntop
      ntop.parent = null
      this.housekeep(op)
      ntop.housekeep(op)
      ntop
    }
    def rotr(op: (T, T) => T): Inner[T] = {
      val ntop = this.left.asInner
      this.left = ntop.right
      this.left.parent = this
      ntop.right = this
      this.parent = ntop
      ntop.parent = null
      this.housekeep(op)
      ntop.housekeep(op)
      ntop
    }
    private def isLeft = parent.left eq this
    def fixUp(op: (T, T) => T): Node[T] = {
      // check if both children are non-null
      // note that both can never be null
      val result = if (left == null) {
        if (parent == null) {
          right.parent = null
          right
        } else {
          if (isLeft) parent.left = right
          else parent.right = right
          right.parent = parent
          parent.fixUp(op)
        }
      } else if (right == null) {
        if (parent == null) {
          left.parent = null
          left
        } else {
          if (isLeft) parent.left = left
          else parent.right = left
          left.parent = parent
          parent.fixUp(op)
        }
      } else {
        housekeep(op)
        val above = this.parent
        val wasLeft = (above ne null) && isLeft
        val n = rebalance(op)
        n.parent = above
        if (above != null) {
          if (wasLeft) above.left = n
          else above.right = n
        }

        if (n.parent != null) n.asInner.parent.fixUp(op)
        else n
      }

      result
    }
    
    def toString(indent: Int) = " " * indent +
      s"Inner($height, \n${left.toString(indent + 2)}, \n${right.toString(indent + 2)})"
    def localString = s"Inner(h = $height, l.h = ${left.height}, r.h = ${right.height})"
  }

  class Leaf[@spec(Int, Long, Double) T](val get: () => T, var parent: Inner[T])
  extends Node[T] {
    def height = 0
    def value = get()
    def pushUp(op: (T, T) => T) {
      if (parent != null) parent.pushUp(op)
    }
    def insert(leaf: Leaf[T], op: (T, T) => T): Node[T] = {
      val inner = new Inner(1, this, leaf, null)
      this.parent = inner
      leaf.parent = inner
      inner.value = op(this.value, leaf.value)
      inner
    }
    def remove(zero: T, op: (T, T) => T): Node[T] = {
      if (parent == null) {
        // the only value left
        new Empty(zero)
      } else {
        def isLeft = parent.left eq this
        if (isLeft) parent.left = null
        else parent.right = null
        parent.fixUp(op)
      }
    }
    def toString(indent: Int) = " " * indent + s"Leaf(${get()})"
    def localString = s"Leaf(${get()})"
  }

  class Empty[@spec(Int, Long, Double) T](val value: T) extends Node[T] {
    def height = 0
    def parent = null
    def parent_=(p: Inner[T]) = throw new IllegalStateException
    def pushUp(op: (T, T) => T) {}
    def insert(leaf: Leaf[T], op: (T, T) => T) = leaf
    def toString(indent: Int) = " " * indent + s"Empty($value)"
    def localString = s"Empty($value)"
  }

}
