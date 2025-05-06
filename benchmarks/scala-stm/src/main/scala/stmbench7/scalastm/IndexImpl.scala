/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package stmbench7.scalastm

import scala.collection.immutable.TreeMap
import scala.jdk.CollectionConverters.SetHasAsJava
import scala.jdk.CollectionConverters.IteratorHasAsJava

import scala.concurrent.stm.Ref

import stmbench7.backend.Index

object IndexImpl {

  class BoxedImmutable[K <: Comparable[K], V] extends Index[K, V] {
    // needed for 2.8, harmless in 2.9
    implicit val order: Ordering[K] = (lhs: K, rhs: K) => lhs compareTo rhs

    private val underlying = Ref(TreeMap.empty[K, V]).single

    override def get(key: K): V = underlying().getOrElse(key, null.asInstanceOf[V])

    override def put(key: K, value: V): Unit = { underlying.transform(_ + (key -> value)) }

    override def putIfAbsent(key: K, value: V): V = {
      underlying
        .getAndTransform({ m => if (m.contains(key)) m else m + (key -> value) })
        .getOrElse(key, null.asInstanceOf[V])
    }

    override def remove(key: K): Boolean =
      underlying transformIfDefined {
        case m if m.contains(key) => m - key
      }

    override def iterator: java.util.Iterator[V] = makeValuesIterator(underlying())

    override def getKeys: java.lang.Iterable[K] = underlying().keySet.asJava

    override def getRange(minKey: K, maxKey: K): java.lang.Iterable[V] =
      new java.lang.Iterable[V] {
        private val range = underlying().range(minKey, maxKey)
        override def iterator: java.util.Iterator[V] = makeValuesIterator(range)
      }

    private def makeValuesIterator(m: TreeMap[K, V]) = {
      m.values.iterator.asJava
    }
  }
}
