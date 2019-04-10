/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package stmbench7.scalastm

import scala.collection.JavaConversions
import scala.concurrent.stm._
import stmbench7.backend.LargeSet

// LargeSetImpl

class LargeSetImpl[A <: Comparable[A]] extends LargeSet[A] {
  val underlying = TMap.empty[A,Unit].single

  def add(e: A) = underlying.put(e, ()).isEmpty
  def remove(e: A) = !underlying.remove(e).isEmpty
  def contains(e: A) = underlying.contains(e)
  def size = underlying.size
  def iterator = JavaConversions.asJavaIterator(underlying.keysIterator)
}
