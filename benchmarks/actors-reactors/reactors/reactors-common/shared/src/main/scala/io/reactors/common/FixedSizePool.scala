package io.reactors
package common



import scala.reflect.ClassTag



class FixedSizePool[T >: Null <: AnyRef: ClassTag](
  val capacity: Int,
  val create: () => T,
  val onRelease: T => Unit
) extends Pool[T] {
  private val queue = new Array[T](capacity + 1)
  private var start = 0
  private var end = 0

  def acquire(): T = {
    if (start != end) {
      val cur = queue(start)
      queue(start) = null
      start = (start + 1) % queue.length
      cur
    } else create()
  }

  def release(x: T): Unit = {
    assert(x != null)
    val nend = (end + 1) % queue.length
    if (nend != start) {
      onRelease(x)
      queue(end) = x
      end = nend
    }
  }
}
