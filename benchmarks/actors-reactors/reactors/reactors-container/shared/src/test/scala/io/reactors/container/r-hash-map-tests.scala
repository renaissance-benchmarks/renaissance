package io.reactors
package container



import java.util.NoSuchElementException
import org.scalacheck._
import org.scalacheck.Gen._
import org.scalacheck.Prop._
import org.scalatest._
import io.reactors.test._
import scala.collection._
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers



class RHashMapCheck extends Properties("RHashMap") with ExtendedProperties {
  val sizes = detChoose(0, 1000)

  property("contain elements") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val table = new RHashMap[Long, String]
      for (i <- 0 until sz) table(i) = i.toString

      assert(table.size == sz)
      for (i <- 0 until sz) assert(table(i) == i.toString, table(i))
      for (i <- 0 until sz / 2) assert(table.remove(i) == true)
      for (i <- 0 until sz / 2) assert(table.get(i) == None)
      for (i <- sz / 2 until sz) assert(table(i) == i.toString, table(i))
      table.clear()
      for (i <- 0 until sz) assert(table.get(i) == None)
      assert(table.size == 0, s"size = ${table.size}")
      true
    }
  }

  property("subscribe to many keys") = forAllNoShrink(sizes, sizes) { (sz, many) =>
    stackTraced {
      val table = new RHashMap[Int, String]
      for (i <- 0 until many) table(i) = i.toString
      val signals = for (i <- 0 until many) yield table.at(i).toEmpty
      for (i <- 0 until sz) table(i) = s"value$i"
      for (i <- 0 until many)
        assert(i >= sz || signals(i)() == s"value$i", signals(i)())
      val moresignals = for (i <- many until sz) yield table.at(i).toEmpty
      for (i <- many until sz) assert(moresignals(i - many)() == s"value$i")
      true
    }
  }

  property("subscribe to non-existing") = forAllNoShrink(sizes, sizes) { (sz, many) =>
    stackTraced {
      val table = new RHashMap[Int, String]
      val signsOfLife = Array.fill(many)(false)
      val subs = for (i <- 0 until many) yield {
        val values = table.at(i)
        values onEvent { _ =>
          signsOfLife(i) = true
        }
      }

      for (i <- 0 until sz) table(i) = "foobar"
      for (i <- 0 until many) assert(i >= sz || signsOfLife(i) == true)
      true
    }
  }

}


class RHashMapSpec extends AnyFlatSpec with Matchers {

  "A RHashMap" should "be empty" in {
    val table = new RHashMap[Long, String]

    table.size should equal (0)
    table.get(0L) should equal (None)
    a [NoSuchElementException] should be thrownBy { table(0L) }
    table.remove(0L) should equal (false)
  }

  it should "contain a single element" in {
    val table = new RHashMap[Long, String]
    table(2L) = 2L.toString

    table.size should equal (1)
    table.get(2L) should equal (Some(2L.toString))
    table.apply(2L) should equal (2L.toString)

    table.remove(2L) should equal (true)
    table.size should equal (0)
  }

  it should "contain two elements" in {
    val table = new RHashMap[Long, String]
    table.update(3L, 3L.toString)
    table.update(4L, 4L.toString)

    table.size should equal (2)
    table.get(3L) should equal (Some(3L.toString))
    table.apply(4L) should equal (4L.toString)
    table.get(5L) should equal (None)
  }

  it should "contain several elements" in {
    containSeveralElements()
  }

  def containSeveralElements() {
    val table = new RHashMap[String, String]
    table.update("a", "1")
    table.update("b", "2")
    table.update("c", "3")
    table.update("d", "4")

    table.size should equal (4)
    table("a") should equal ("1")
    table("b") should equal ("2")
    table("c") should equal ("3")
    table("d") should equal ("4")

    table.remove("b") should equal (true)
    table.remove("c") should equal (true)
    table("a") should equal ("1")
    table("d") should equal ("4")
  }

  it should "subscribe to a specific key" in {
    val many = 512
    val table = new RHashMap[Int, String]
    for (i <- 0 until many) table(i) = i.toString
    val atSpecificKey = table.at(128).toEmpty

    table(128) = "new value"
    atSpecificKey() should equal ("new value")
  }

}
