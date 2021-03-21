package io.reactors
package container



import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop._
import scala.collection._



class RBinaryHeapCheck extends Properties("RBinaryHeap") with ExtendedProperties {

  val sizes = detChoose(0, 1000)

  property("react to head changes") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val q = new RBinaryHeap[Int]
      val buffer = mutable.Buffer[Int]()
      val heads = q.head.tail.onEvent(buffer += _)

      for (i <- (0 until size).reverse) q.enqueue(i)

      for (i <- 0 until size) {
        assert(q.dequeue() == i)
        if (i < (size - 1)) {
          assert(q.head() == i + 1)
        }
      }

      s"buffer contents ok: $buffer" |:
        buffer == ((0 until size).reverse ++ (1 until size) ++ Seq(q.nil))
    }
  }

}
