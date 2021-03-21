package io.reactors
package container



import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop._
import scala.collection._



class RRingCheck extends Properties("RRing") with ExtendedProperties {

  val sizes = detChoose(1, 1000)

  property("correctly show availability") = forAllNoShrink(sizes, sizes) {
    (size, window) =>
    stackTraced {
      val ring = new RRing[Int](window)
      val dequeued = mutable.Buffer[Int]()

      ring.available.is(false) on {
        while (ring.nonEmpty) dequeued += ring.dequeue()
      }

      for (i <- 0 until size) ring.enqueue(i)
      assert(dequeued == (0 until (size - size % window)))
      while (ring.nonEmpty) dequeued += ring.dequeue()

      dequeued == (0 until size)
    }
  }

}