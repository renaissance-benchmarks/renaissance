package io.reactors
package common



import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Gen.choose
import org.scalatest._
import scala.collection._
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers



class UnrolledRingSpec extends AnyFlatSpec with Matchers {

  "UnrolledRing" should "be empty" in {
    val ring = new UnrolledRing[String]

    ring.isEmpty should be (true)
    ring.nonEmpty should be (false)
  }

  it should "enqueue and dequeue an element" in {
    val ring = new UnrolledRing[String]

    ring.enqueue("first")
    ring.isEmpty should be (false)
    ring.head should be ("first")
    ring.dequeue() should be ("first")
    ring.isEmpty should be (true)
  }

  it should "enqueue and dequeue many elements" in {
    val ring = new UnrolledRing[String]

    ring.isEmpty should equal (true)
    for (x <- 0 until 1024) {
      ring.enqueue(x.toString)
      ring.isEmpty should equal (false)
    }
    ring.size should equal(1024)
    for (x <- 0 until 1024) {
      ring.isEmpty should equal (false)
      ring.dequeue() should equal (x.toString)
    }
    ring.isEmpty should equal (true)
  }

  it should "randomly enqueue and dequeue elements" in {
    import scala.collection._
    val ring = new UnrolledRing[String]
    val elems = for (x <- 0 until 1024) yield x.toString
    val input = elems.to[mutable.Queue]
    val plan = Seq(
      4, -2, 4, -2, 8, -4, 16, -16, 64, -8, 64, -128, 32, -32, 64, -64, 512, -256, 128,
      -256, 64, -192, 32, -16, 32, -48)
    val buffer = mutable.Buffer[String]()

    var count = 0
    for (n <- plan) {
      count += n
      if (n > 0) for (_ <- 0 until n) ring.enqueue(input.dequeue)
      else for (_ <- 0 until -n) buffer += ring.dequeue()
    }
    count should equal (0)

    buffer should equal (elems)
  }

  it should "traverse the elements using foreach" in {
    import scala.collection._
    val ring = new UnrolledRing[Int]
    val queue = mutable.Queue[Int]()
    for (i <- 0 until 200) {
      ring.enqueue(i)
      queue.enqueue(i)
      val buffer = mutable.ArrayBuffer[Int]()
      ring.foreach(x => buffer += x)
      buffer should equal (queue)
      ring.size should equal (queue.size)
    }
  }

  it should "remove elements" in {
    import scala.collection._
    val size = 200
    val ring = new UnrolledRing[Int]
    val set = mutable.Set[Int]()
    for (i <- 0 until size) {
      ring.enqueue(i)
      set += i
    }
    for (i <- 0 until size by 10) {
      ring.remove(i) should equal (i - i / 10)
      set -= i
    }

    val checkSet = mutable.Set[Int]()
    for (x <- ring) checkSet += x
    checkSet should equal (set)

    for (i <- 0 until size) {
      val at = ring.remove(i)
      (at != -1) should equal (set(i))
    }

    ring.size should equal (0)
    ring.isEmpty should equal (true)

    val smallsize = 2
    for (i <- 0 until 2) ring.enqueue(i)
    for (i <- 0 until 2) ring.remove(i) should equal (0)

    ring.size should equal (0)

    for (i <- 0 until size) ring.enqueue(i)
    for (i <- (size - 1) to 0 by -1) ring.remove(i) should equal(i)

    ring.size should equal (0)
  }

}


class UnrolledRingCheck extends Properties("UnrolledRing") with ExtendedProperties {

  val smallSizes = detChoose(0, UnrolledRing.INITIAL_NODE_LENGTH)

  val sizes = detChoose(0, 1000)

  val probs = detChoose(0, 100)

  property("should enqueue elements and traverse them") = forAllNoShrink(sizes) {
    size =>
    stackTraced {
      val buffer = new UnrolledRing[Int]

      for (i <- 0 until size) buffer.enqueue(i)

      val seen = mutable.Buffer[Int]()
      buffer.foreach(seen += _)

      val extracted = mutable.Buffer[Int]()
      while (buffer.nonEmpty) extracted += buffer.dequeue()

      seen == (0 until size) && extracted == (0 until size)
    }
  }

  property("should randomly enqueue and dequeue") = forAllNoShrink(sizes, probs) {
    (size, prob) =>
    stackTraced {
      val random = new scala.util.Random(size)
      val buffer = new UnrolledRing[Int]

      val extracted = mutable.Buffer[Int]()
      for (i <- 0 until size) {
        buffer.enqueue(i)
        if (random.nextInt(100) < prob && buffer.nonEmpty) extracted += buffer.dequeue()
      }
      while (buffer.nonEmpty) extracted += buffer.dequeue()

      extracted == (0 until size)
    }
  }

  property("should never have more than 2 nodes") = forAllNoShrink(smallSizes, sizes) {
    (startsize, size) =>
    stackTraced {
      val buffer = new UnrolledRing[Int]

      for (i <- 0 until startsize) buffer.enqueue(i)

      val extracted = mutable.Buffer[Int]()
      for (i <- 0 until size) {
        buffer.enqueue(i)
        extracted += buffer.dequeue()
      }
      while (buffer.nonEmpty) extracted += buffer.dequeue()

      extracted == ((0 until startsize) ++ (0 until size)) && buffer.nodes.size <= 3
    }
  }

}
