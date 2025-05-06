/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package stmbench7.scalastm

import scala.jdk.CollectionConverters.IteratorHasAsJava

import stmbench7.backend.ImmutableCollection

class ImmutableSeqImpl[A](contents: Seq[A]) extends ImmutableCollection[A] {
  override def clone: ImmutableCollection[A] = this
  override def contains(element: A): Boolean = contents.contains(element)
  override def size: Int = contents.size
  override def iterator: java.util.Iterator[A] = contents.iterator.asJava
}
