package io.reactors
package container



import io.reactors.algebra.Commute
import scala.collection._



/** Stores elements that form a commutative monoid.
 *
 *  Elements are incrementally aggregated using a binary operator
 *  that is associative and commutative. The value of the aggregation
 *  can be accessed with the `signal` method.
 */
class CommuteCatamorph[@spec(Int, Long, Double) T, @spec(Int, Long, Double) S](
  val get: S => T, val zero: T, val op: (T, T) => T
) extends RCatamorph[T, S] with RContainer.Modifiable {
  import CommuteCatamorph._

  private[reactors] var subscription: Subscription = _
  private[reactors] var root: Node[T] = null
  private[reactors] var leaves: mutable.Map[S, Leaf[T]] = null
  private val insertsEmitter = new Events.Emitter[S]
  private val removesEmitter = new Events.Emitter[S]
  private var rootValue: RCell[T] = null

  def inserts: Events[S] = insertsEmitter

  def removes: Events[S] = removesEmitter

  def init(s: CommuteCatamorph[T, S]) {
    root = new Empty(zero)
    leaves = mutable.Map[S, Leaf[T]]()
    rootValue = RCell(root.value)
    subscription = Subscription.empty
  }

  init(this)

  def unsubscribe() = subscription.unsubscribe()

  def signal: Signal[T] = rootValue

  protected def newLeaf(v: S, f: S => T) = new Leaf[T](() => f(v), null)

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


object CommuteCatamorph {

  def apply[@spec(Int, Long, Double) T](implicit m: Commute[T]) =
    new CommuteCatamorph[T, T](v => v, m.zero, m.operator)

  implicit def factory[@spec(Int, Long, Double) T: Commute] =
    new RContainer.Factory[T, CommuteCatamorph[T, T]] {
      def apply(inserts: Events[T], removes: Events[T]): CommuteCatamorph[T, T] = {
        val m = implicitly[Commute[T]]
        val mc = new CommuteCatamorph[T, T](v => v, m.zero, m.operator)
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
    def housekeep(op: (T, T) => T) {}
    def toString(indent: Int): String
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
    private def heightOf(l: Node[T], r: Node[T]) = 1 + math.max(l.height, r.height)
    override def housekeep(op: (T, T) => T) {
      height = heightOf(left, right)
      value = op(left.value, right.value)
    }
    def insert(leaf: Leaf[T], op: (T, T) => T): Node[T] = {
      if (left.height < right.height) {
        left = left.insert(leaf, op)
        left.parent = this
      } else {
        right = right.insert(leaf, op)
        right.parent = this
      }
      housekeep(op)
      this
    }
    def fix(op: (T, T) => T): Node[T] = {
      // Check if both children are non-null.
      // Note that both can never be null.
      def isLeft = parent.left eq this
      val result = if (left == null) {
        if (parent == null) {
          right.parent = null
          right
        } else {
          if (isLeft) parent.left = right
          else parent.right = right
          right.parent = parent
          parent.fix(op)
        }
      } else if (right == null) {
        if (parent == null) {
          left.parent = null
          left
        } else {
          if (isLeft) parent.left = left
          else parent.right = left
          left.parent = parent
          parent.fix(op)
        }
      } else {
        // Check if unbalanced.
        val lheight = left.height
        val rheight = right.height
        val diff = lheight - rheight
        
        // See if rebalancing is necessary.
        if (diff > 1) {
          // Note that this means left is inner.
          val leftInner = left.asInstanceOf[Inner[T]]
          if (leftInner.left.height > leftInner.right.height) {
            // New left is the bigger left grandchild.
            val nleft = leftInner.left
            nleft.parent = this
            // New right is an inner node above the right child
            // and the smaller left grandchild.
            val nright =
              new Inner(heightOf(leftInner.right, right), leftInner.right, right, this)
            nright.left.parent = nright
            nright.right.parent = nright
            // And we update the children.
            left = nleft
            right = nright
          } else {
            // Everything mirrored.
            val nleft = leftInner.right
            nleft.parent = this
            val nright =
              new Inner(heightOf(leftInner.left, right), leftInner.left, right, this)
            nright.left.parent = nright
            nright.right.parent = nright
            left = nleft
            right = nright
          }
        } else if (diff < -1) {
          // Note that this means right is inner -- everything mirrored.
          val rightInner = right.asInstanceOf[Inner[T]]
          if (rightInner.left.height > rightInner.right.height) {
            val nright = rightInner.left
            nright.parent = this
            val nleft =
              new Inner(heightOf(rightInner.right, left), rightInner.right, left, this)
            nleft.left.parent = nleft
            nleft.right.parent = nleft
            left = nleft
            right = nright
          } else {
            val nright = rightInner.right
            nright.parent = this
            val nleft =
              new Inner(heightOf(rightInner.left, left), rightInner.left, left, this)
            nleft.left.parent = nleft
            nleft.right.parent = nleft
            left = nleft
            right = nright
          }
        }

        housekeep(op)

        if (parent != null) parent.fix(op)
        else this
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
        // The only value left.
        new Empty(zero)
      } else {
        def isLeft = parent.left eq this
        if (isLeft) parent.left = null
        else parent.right = null
        parent.fix(op)
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
