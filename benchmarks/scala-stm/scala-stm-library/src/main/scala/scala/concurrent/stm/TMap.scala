/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import scala.collection.{immutable, mutable, generic}
import mutable.Iterable


object TMap {

  object View extends generic.MutableMapFactory[TMap.View] {

    implicit def canBuildFrom[A, B]: generic.CanBuildFrom[Coll, (A, B), TMap.View[A, B]] = new MapCanBuildFrom[A, B]

    def empty[A, B] = TMap.empty[A, B].single

    override def newBuilder[A, B] = new mutable.Builder[(A, B), View[A, B]] {
      private val underlying = TMap.newBuilder[A, B]

      def clear() { underlying.clear() }
      def += (kv: (A, B)): this.type = { underlying += kv ; this }
      def result() = underlying.result().single
    }

    override def apply[A, B](kvs: (A, B)*): TMap.View[A, B] = (TMap.newBuilder[A, B] ++= kvs).result().single
  }

  /** A `Map` that provides atomic execution of all of its methods. */
  trait View[A, B] extends mutable.Map[A, B] with mutable.MapLike[A, B, View[A, B]] with TxnDebuggable {
    /** Returns the `TMap` perspective on this transactional map, which
     *  provides map functionality only inside atomic blocks.
     */
    def tmap: TMap[A, B]

    def clone: TMap.View[A, B]

    /** Takes an atomic snapshot of this transactional map. */
    def snapshot: immutable.Map[A, B]

    override def empty: View[A, B] = TMap.empty[A, B].single

    override protected[this] def newBuilder: mutable.Builder[(A, B), View[A, B]] = View.newBuilder[A, B]

    override def stringPrefix = "TMap"
  }


  /** Constructs and returns a new empty `TMap`. */
  def empty[A, B]: TMap[A, B] = impl.STMImpl.instance.newTMap[A, B]

  /** Returns a builder of `TMap`. */
  def newBuilder[A, B]: mutable.Builder[(A, B), TMap[A, B]] = impl.STMImpl.instance.newTMapBuilder[A, B]

  /** Constructs and returns a new `TMap` that will contain the key/value pairs
   *  from `kvs`.
   */
  def apply[A, B](kvs: (A, B)*): TMap[A, B] = (newBuilder[A, B] ++= kvs).result()


  /** Allows a `TMap` in a transactional context to be used as a `Map`. */
  implicit def asMap[A, B](m: TMap[A, B])(implicit txn: InTxn): View[A, B] = m.single
}


/** A transactional map implementation that requires that all of its map-like
 *  operations be called from inside an atomic block.  Rather than extending
 *  `Map`, an implicit conversion is provided from `TMap` to `Map` if the
 *  current scope is part of an atomic block (see `TMap.asMap`).
 *
 *  The keys (with type `A`) must be immutable, or at least not modified while
 *  they are in the map.  The `TMap` implementation assumes that it can safely
 *  perform key equality and hash checks outside a transaction without
 *  affecting atomicity. 
 *
 *  @author Nathan Bronson
 */
trait TMap[A, B] extends TxnDebuggable {

  /** Returns an instance that provides transactional map functionality without
   *  requiring that operations be performed inside the static scope of an
   *  atomic block.
   */
  def single: TMap.View[A, B]

  def clone(implicit txn: InTxn): TMap[A, B] = single.clone.tmap

  // The following method work fine via the asMap mechanism, but is important
  // enough that we don't want the implicit conversion to make it invisible to
  // ScalaDoc or IDE auto-completion

  def snapshot: immutable.Map[A, B] = single.snapshot

  // The following methods work fine via the asMap mechanism, but are heavily
  // used.  We add transactional versions of them to allow overrides to get
  // access to the InTxn instance without a ThreadLocal lookup.

  def isEmpty(implicit txn: InTxn): Boolean
  def size(implicit txn: InTxn): Int
  def foreach[U](f: ((A, B)) => U)(implicit txn: InTxn)
  def contains(key: A)(implicit txn: InTxn): Boolean
  def apply(key: A)(implicit txn: InTxn): B
  def get(key: A)(implicit txn: InTxn): Option[B]
  def update(key: A, value: B)(implicit txn: InTxn) { put(key, value) }
  def put(key: A, value: B)(implicit txn: InTxn): Option[B]
  def remove(key: A)(implicit txn: InTxn): Option[B]

  // The following methods return the wrong receiver when invoked via the asMap
  // conversion.  They are exactly the methods of mutable.Map whose return type
  // is this.type.  Note that there are other methods of mutable.Map that we
  // allow to use the implicit mechanism, such as getOrElseUpdate(k).
  
  def += (kv: (A, B))(implicit txn: InTxn): this.type = { put(kv._1, kv._2) ; this }
  def += (kv1: (A, B), kv2: (A, B), kvs: (A, B)*)(implicit txn: InTxn): this.type = { this += kv1 += kv2 ++= kvs }
  def ++= (kvs: TraversableOnce[(A, B)])(implicit txn: InTxn): this.type = { for (kv <- kvs) this += kv ; this }
  def -= (k: A)(implicit txn: InTxn): this.type = { remove(k) ; this }
  def -= (k1: A, k2: A, ks: A*)(implicit txn: InTxn): this.type = { this -= k1 -= k2 --= ks }
  def --= (ks: TraversableOnce[A])(implicit txn: InTxn): this.type = { for (k <- ks) this -= k ; this }

  def transform(f: (A, B) => B)(implicit txn: InTxn): this.type
  def retain(p: (A, B) => Boolean)(implicit txn: InTxn): this.type
}
