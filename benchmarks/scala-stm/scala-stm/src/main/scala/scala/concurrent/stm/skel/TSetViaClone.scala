/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package skel

import scala.collection.{immutable, mutable}

private[stm] object TSetViaClone {
  class FrozenMutableSet[A](self: mutable.Set[A]) extends immutable.Set[A] {
    override def isEmpty: Boolean = self.isEmpty
    override def size: Int = self.size
    def contains(key: A): Boolean = self.contains(key)
    def iterator: Iterator[(A)] = self.iterator
    override def foreach[U](f: A => U) { self foreach f }
    def + (x: A): immutable.Set[A] = new FrozenMutableSet(self.clone() += x)
    def - (x: A): immutable.Set[A] = new FrozenMutableSet(self.clone() -= x)
  }
}

/** Provides an implementation for the bulk of the functionality of `TSet` and
 *  `TSet.View` by making extensive use of `clone()`.  Assumes that the
 *  underlying implementation of `clone()` is O(1).
 *
 *  @author Nathan Bronson
 */
private[stm] trait TSetViaClone[A] extends TSet.View[A] with TSet[A] {
  import TSetViaClone._

  // Implementations may be able to do better.
  override def snapshot: immutable.Set[A] = new FrozenMutableSet(clone())

  def tset: TSet[A] = this
  def single: TSet.View[A] = this

  /** Something like `"TSet[size=3](3, 1, 10)"`, stopping after 1K chars */
  def dbgStr: String = atomic.unrecorded({ _ => mkStringPrefix("TSet", single) }, { _.toString })

  /** Returns an array of elements, since that is likely to be the
   *  easiest to examine in a debugger.  Also, this avoids problems with
   *  relying on copy-on-write after discarding `Ref` writes.
   */
  def dbgValue: Any = atomic.unrecorded({ _ => toArray[Any] }, { x => x })

  //////////// builder functionality (from mutable.SetLike via TSet.View)

  override protected[this] def newBuilder: TSet.View[A] = empty

  override def result(): TSet.View[A] = this


  //////////// construction of new TSets

  // A cheap clone() means that mutable.SetLike's implementations of +, ++,
  // -, and -- are all pretty reasonable.

  override def clone: TSet.View[A]

  //////////// atomic compound ops

  override def retain(p: A => Boolean) {
    atomic { implicit txn =>
      for (x <- tset)
        if (!p(x))
          tset -= x
    }
  }
}
