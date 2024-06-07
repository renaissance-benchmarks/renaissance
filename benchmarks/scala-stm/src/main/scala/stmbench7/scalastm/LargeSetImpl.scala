/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package stmbench7.scalastm

import scala.jdk.CollectionConverters.IteratorHasAsJava

import scala.concurrent.stm.TMap

import stmbench7.backend.LargeSet

class LargeSetImpl[A <: Comparable[A]] extends LargeSet[A] {
  private val underlying = TMap.empty[A, Unit].single

  override def add(e: A): Boolean = underlying.put(e, ()).isEmpty
  override def remove(e: A): Boolean = underlying.remove(e).isDefined
  override def contains(e: A): Boolean = underlying.contains(e)
  override def size: Int = underlying.size
  override def iterator: java.util.Iterator[A] = underlying.keysIterator.asJava
}
