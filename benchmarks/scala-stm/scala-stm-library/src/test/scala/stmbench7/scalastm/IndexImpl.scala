/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package stmbench7.scalastm

import scala.annotation._
import scala.collection.immutable.TreeMap
import scala.collection.mutable.ArrayBuffer
import scala.collection.JavaConversions
import scala.concurrent.stm._
import stmbench7.backend.Index

object IndexImpl {
  class BoxedImmutable[A <: Comparable[A], B] extends Index[A,B] {
    // needed for 2.8, harmless in 2.9
    implicit val order = new Ordering[A] {
      def compare(lhs: A, rhs: A) = lhs compareTo rhs
    }

    val underlying = Ref(TreeMap.empty[A,B]).single

    def get(key: A) = underlying().getOrElse(key, null.asInstanceOf[B])

    def put(key: A, value: B) { underlying.transform(_ + (key -> value)) }

    def putIfAbsent(key: A, value: B): B = {
      underlying.getAndTransform({ m => if (m.contains(key)) m else m + (key -> value) }).getOrElse(key, null.asInstanceOf[B])
    }

    def remove(key: A) = underlying transformIfDefined {
      case m if m.contains(key) => m - key
    }

    def iterator = makeValuesIterator(underlying())

    def getKeys = JavaConversions.setAsJavaSet(underlying().keySet)

    def getRange(minKey: A, maxKey: A) = new java.lang.Iterable[B] {
      val range = underlying().range(minKey, maxKey)
      def iterator = makeValuesIterator(range)
    }

    private def makeValuesIterator(m: TreeMap[A, B]) = {
      JavaConversions.asJavaIterator(m.values.iterator)
    }
  }
}
