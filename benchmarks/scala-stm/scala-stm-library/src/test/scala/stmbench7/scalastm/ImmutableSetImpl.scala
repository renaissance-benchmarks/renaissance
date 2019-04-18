/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package stmbench7.scalastm

import scala.collection.JavaConversions
import scala.concurrent.stm._
import stmbench7.backend.ImmutableCollection

/** Read-only wrapper */
class ImmutableSetImpl[A](contents: TSet.View[A], shared: Boolean = true) extends ImmutableCollection[A] {
  override def clone: ImmutableSetImpl[A] = if (!shared) this else new ImmutableSetImpl(contents.clone(), false)
  def contains(element: A) = contents.contains(element)
  def size = contents.size
  def iterator = JavaConversions.asJavaIterator(contents.iterator)
}
