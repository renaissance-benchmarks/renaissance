package io.reactors
package common



import scala.collection._
import scala.reflect.ClassTag



/** A collection that is a set and a sequence.
 */
class SetSeq[T >: Null <: AnyRef] extends Seq[T] {
  private val buffer = mutable.ArrayBuffer[T]()
  private val index = mutable.Map[T, Int]()

  def length = buffer.length

  def apply(i: Int) = buffer(i)

  def iterator = buffer.iterator

  def +=(x: T): this.type = {
    if (!index.contains(x)) {
      buffer += x
      index(x) = buffer.length - 1
    }
    this
  }

  def -=(x: T): this.type = {
    if (index.contains(x)) {
      val idx = index(x)
      val last = buffer.last
      buffer(idx) = last
      buffer.remove(buffer.length - 1)
      index(last) = idx
      index.remove(x)
    }
    this
  }
}
