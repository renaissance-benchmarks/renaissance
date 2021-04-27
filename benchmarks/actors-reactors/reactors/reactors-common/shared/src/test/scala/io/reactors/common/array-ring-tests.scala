package io.reactors.common



import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import scala.collection._
import scala.util.Random



class ArrayRingCheck extends Properties("ArrayRing") with ExtendedProperties {

  val sizes = detChoose(1, 1000)

  val probs = detChoose(0, 100)

  property("should enqueue and traverse elements") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val ring = new ArrayRing[Int](size)

      for (i <- 0 until size) ring.enqueue(i)
      for (i <- 0 until size) assert(ring(i) == i)

      true
    }
  }

  property("should enqueue and dequeue elements") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val ring = new ArrayRing[Int](size)

      for (i <- 0 until size) {
        ring.enqueue(i)
        assert(ring.size == i + 1)
      }
      for (i <- 0 until size) assert(ring.dequeue() == i)

      true
    }
  }

  property("should enqueue and dequeueMany") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val ring = new ArrayRing[Int](size)

      for (i <- 0 until size) ring.enqueue(i)
      ring.dequeueMany(size / 2)

      ring.size == (size - size / 2)
    }
  }

  property("should randomly enqueue and dequeue") = forAllNoShrink(sizes, probs) {
    (size, prob) =>
    stackTraced {
      val elements = mutable.ArrayBuffer[Int]()
      val dequeued = mutable.ArrayBuffer[Int]()
      val ring = new ArrayRing[Int](size)
      val rand = new Random(size * prob)

      for (i <- 0 until size) {
        elements += i
        ring.enqueue(i)
        while (rand.nextInt(100) < prob && ring.nonEmpty) {
          dequeued += ring.dequeue()
        }
      }
      while (ring.nonEmpty) {
        dequeued += ring.dequeue()
      }

      elements == dequeued
    }
  }

  property("should randomly clear") = forAllNoShrink(sizes, probs) {
    (size, prob) =>
    stackTraced {
      val elements = mutable.ArrayBuffer[Int]()
      val dequeued = mutable.ArrayBuffer[Int]()
      val ring = new ArrayRing[Int](size)
      val rand = new Random(size * prob)
      var cleared = false

      for (i <- 0 until size) {
        if (cleared) elements += i
        ring.enqueue(i)
        if (!cleared && rand.nextInt(100) < prob) {
          ring.clear()
          assert(ring.isEmpty)
          assert(ring.size == 0)
          cleared = true
        }
      }
      while (ring.nonEmpty) {
        dequeued += ring.dequeue()
      }

      !cleared || elements == dequeued
    }
  }

  property("should flush when full") = forAllNoShrink(sizes, sizes) {
    (size, total) =>
    stackTraced {
      val elements = mutable.ArrayBuffer[Int]()
      val dequeued = mutable.ArrayBuffer[Int]()
      val ring = new ArrayRing[Int](size)

      for (i <- 0 until total) {
        elements += i
        ring.enqueue(i)
        assert(ring.last == i)
        if (ring.size == size) {
          while (ring.nonEmpty) {
            dequeued += ring.dequeue()
          }
        }
      }
      while (ring.nonEmpty) {
        dequeued += ring.dequeue()
      }

      elements == dequeued
    }
  }

  property("should resize") = forAllNoShrink(sizes) { total =>
    stackTraced {
      val elements = mutable.ArrayBuffer[Int]()
      val dequeued = mutable.ArrayBuffer[Int]()
      val ring = new ArrayRing[Int]

      for (i <- 0 until total) {
        elements += i
        ring.enqueue(i)
        assert(ring.last == i)
      }
      while (ring.nonEmpty) {
        dequeued += ring.dequeue()
      }

      elements == dequeued
    }
  }
}
