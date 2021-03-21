package io.reactors
package common



import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Gen.choose
import scala.collection._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers



class UnrolledBufferTest extends AnyFunSuite with Matchers {

  test("enqueue and dequeue many elements") {
    val b = new UnrolledBuffer[String]()
    for (i <- 0 until 1000) b.enqueue(i.toString)
    for (i <- 0 until 1000) assert(b.dequeue() == i.toString)
  }

}


class UnrolledBufferCheck extends Properties("UnrolledBuffer") with ExtendedProperties {

  val sizes = detChoose(0, 1000)

  property("should enqueue elements and traverse them") = forAllNoShrink(sizes) {
    size =>
    stackTraced {
      val buffer = new UnrolledBuffer[Int]

      for (i <- 0 until size) buffer.enqueue(i)

      val seen = mutable.Buffer[Int]()
      buffer.foreach(seen += _)

      val extracted = mutable.Buffer[Int]()
      while (buffer.nonEmpty) extracted += buffer.dequeue()

      seen == (0 until size) && extracted == (0 until size)
    }
  }

}
