package io.reactors
package container



import io.reactors.test._
import java.util.NoSuchElementException
import org.scalacheck._
import org.scalacheck.Gen._
import org.scalacheck.Prop._
import org.scalatest._
import scala.collection._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers



class RHashSetCheck extends Properties("RHashSet") with ExtendedProperties {
  val sizes = detChoose(0, 1000)

  property("basic ops") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val table = new RHashSet[Long]
      for (i <- 0 until sz) table += i

      assert(table.size == sz)
      for (i <- 0 until sz) assert(table(i))
      for (i <- 0 until sz / 2) assert(table -= i)
      for (i <- 0 until sz / 2) assert(!table(i))
      for (i <- sz / 2 until sz) assert(table(i))
      table.clear()
      for (i <- 0 until sz) assert(!table(i))
      assert(table.size == 0, s"size = ${table.size}")
      true
    }
  }

  property("traverse") = forAllNoShrink(sizes) { sz =>
    val table = new RHashSet[Long]
    for (i <- 0 until sz) table += i

    val seen = mutable.Buffer[Long]()
    for (x <- table) seen += x
    seen.size == sz && seen.toSet == (0 until sz).toSet
  }

}


class RHashSetSpec extends AnyFunSuite with Matchers {

  test("be empty") {
    val table = new RHashSet[Long]

    assert(table.size == 0)
    assert(!table(0L))
    assert(table.remove(0L) == false)
  }

  test("contain a single element") {
    val table = new RHashSet[Long]
    table += 2L

    assert(table.size == 1)
    assert(table(2L))

    assert(table.remove(2L) == true)
    assert(table.size == 0)
  }

  test("contain two elements") {
    val table = new RHashSet[Long]
    table += 3L
    table += 4L

    assert(table.size == 2)
    assert(table(3L))
    assert(table(4L))
    assert(!table(5L))
  }

}
