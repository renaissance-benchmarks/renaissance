/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package stmbench7.scalastm

import scala.jdk.CollectionConverters.IteratorHasAsJava

import scala.concurrent.stm.TSet

import stmbench7.backend.ImmutableCollection

/** Read-only wrapper */
class ImmutableSetImpl[A](contents: TSet.View[A], shared: Boolean = true)
  extends ImmutableCollection[A] {

  override def clone: ImmutableCollection[A] =
    if (!shared) this else new ImmutableSetImpl(contents.clone(), false)

  override def contains(element: A): Boolean = contents.contains(element)
  override def size: Int = contents.size
  override def iterator: java.util.Iterator[A] = contents.iterator.asJava
}
