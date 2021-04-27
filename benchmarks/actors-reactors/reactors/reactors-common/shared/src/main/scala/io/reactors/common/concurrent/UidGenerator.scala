package io.reactors
package common
package concurrent



import java.util.concurrent.atomic._
import scala.annotation.tailrec



class UidGenerator(val scalability: Int) {
  private val chunkSize = 128
  private val mainCounter = new AtomicLong(0L)
  private val localCounters = new AtomicLongArray(scalability)

  /** Generates a unique numeric identifier.
   *
   *  The numbers are picked so that they are as sequential as possible, but do not
   *  necessarily come one after the other.
   */
  def generate(): Long = {
    val pos = Thread.currentThread.getId.toInt % localCounters.length()

    @tailrec def get(): Long = {
      val v = localCounters.get(pos)
      if (v % chunkSize == 0) {
        val newStart = mainCounter.getAndAdd(chunkSize)
        localCounters.compareAndSet(pos, v, newStart + 1)
        get()
      } else {
        if (localCounters.compareAndSet(pos, v, v + 1)) {
          v
        } else {
          get()
        }
      }
    }

    get()
  }
}
