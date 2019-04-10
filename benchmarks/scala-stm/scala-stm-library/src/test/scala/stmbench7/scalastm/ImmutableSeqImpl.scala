/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package stmbench7.scalastm

import scala.collection.JavaConversions
import stmbench7.backend.ImmutableCollection

class ImmutableSeqImpl[A](contents: Seq[A]) extends ImmutableCollection[A] {
  override def clone = this
  def contains(element: A) = contents.contains(element)
  def size = contents.size
  def iterator = JavaConversions.asJavaIterator(contents.iterator)
}
