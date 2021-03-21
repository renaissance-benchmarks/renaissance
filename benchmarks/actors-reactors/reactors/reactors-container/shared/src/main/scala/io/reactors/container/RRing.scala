package io.reactors
package container



import io.reactors.common.ArrayRing



class RRing[@spec(Int, Long, Double) T: Arrayable](val window: Int) {
  private var ring: ArrayRing[T] = _
  private var rawSize: RCell[Int] = _
  private var rawAvailable: Signal[Boolean] = _

  def init(self: RRing[T]): Unit = {
    ring = new ArrayRing[T](window)
    rawSize = RCell(0)
    rawAvailable = rawSize.map(_ < window).changed(true).toSignal(true)
  }

  init(this)

  def sizes: Signal[Int] = rawSize

  def available: Signal[Boolean] = rawAvailable

  def size: Int = rawSize()

  def isEmpty: Boolean = size == 0

  def nonEmpty: Boolean = !isEmpty

  def apply(idx: Int): T = ring(idx)

  def enqueue(x: T): Unit = {
    ring.enqueue(x)
    rawSize := rawSize() + 1
  }

  def dequeue(): T = {
    val x = ring.dequeue()
    rawSize := rawSize() - 1
    x
  }

  def dequeueMany(n: Int): Unit = {
    ring.dequeueMany(n)
    rawSize := rawSize() - n
  }

  def clear(): Unit = {
    ring.clear()
    rawSize := 0
  }
}
