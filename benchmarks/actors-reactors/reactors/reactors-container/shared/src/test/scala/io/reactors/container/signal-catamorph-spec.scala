package io.reactors
package container



import org.scalacheck._
import org.scalacheck.Gen._
import org.scalacheck.Prop._
import org.scalatest._
import io.reactors.algebra._
import io.reactors.test._
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.matchers.should.Matchers



class SignalCatamorphCheck extends Properties("SignalCatamorph")
with ExtendedProperties {

  val sizes = detChoose(0, 100)

  plus("Int Monoid", SignalCatamorph(Monoid(0)(_ + _)))

  concat("String Monoid", SignalCatamorph(Monoid("")(_ + _)))

  plus("Int Commute", SignalCatamorph(Commute(0)(_ + _)))

  plus("Int Abelian", SignalCatamorph(Abelian(0)(_ + _)(_ - _)))

  def concat(structure: String, newSignalCatamorph: =>SignalCatamorph[String]) {
    property(s"${structure}: add signals") = forAllNoShrink(sizes) { size =>
      stackTraced {
        val catamorph = newSignalCatamorph
        val cells = for (i <- 0 until size) yield new RCell(i + " ")
        for ((c, i) <- cells.zipWithIndex) {
          catamorph += c
          assert(catamorph.signal() == ((0 to i).foldLeft("")(_ + _ + " ")))
        }
        true
      }
    }

    property(s"${structure}: remove signals") = forAllNoShrink(sizes) { size =>
      stackTraced {
        val catamorph = newSignalCatamorph
        val cells = for (i <- 0 until size) yield new RCell(i + " ")
        for (c <- cells) catamorph += c
        for ((c, i) <- cells.zipWithIndex; if (i % 2 == 0)) {
          catamorph -= c
          val expected =
            (0 until size).filter(x => x % 2 == 1 || x > i).foldLeft("")(_ + _ + " ")
          assert(catamorph.signal() == expected)
        }
        true
      }
    }
  }

  def plus(structure: String, newSignalCatamorph: =>SignalCatamorph[Int]) {
    property(s"$structure: reflect signals") = forAllNoShrink(sizes) { size =>
      stackTraced {
        val catamorph = newSignalCatamorph
        val cells = for (_ <- 0 until size) yield RCell(0)
        for (c <- cells) catamorph += c
  
        assert(catamorph.signal() == 0)
        for ((c, i) <- cells.zipWithIndex) c := i
        assert(catamorph.signal() == cells.length * (cells.length - 1) / 2)
        if (size > 10) {
          cells(10) := 0
          assert(catamorph.signal() == cells.length * (cells.length - 1) / 2 - 10)
        }
        true
      }
    }
  
    property(s"$structure: reflect addition of new signals") = forAllNoShrink(sizes) {
      size =>
      stackTraced {
        val catamorph = newSignalCatamorph
        val cells = for (i <- 0 until size) yield RCell(i)
        for (c <- cells) catamorph += c
  
        def total(n: Int) = n * (n - 1) / 2
        assert(catamorph.signal() == total(cells.length))
        catamorph += RCell(size + 0)
        assert(catamorph.signal() == total(cells.length + 1))
        catamorph += RCell(size + 1)
        assert(catamorph.signal() == total(cells.length + 2))
        catamorph += RCell(size + 2)
        assert(catamorph.signal() == total(cells.length + 3))
        catamorph += RCell(size + 3)
        assert(catamorph.signal() == total(cells.length + 4))
        true
      }
    }
  
    property(s"$structure: reflect removal of signals") = forAllNoShrink(sizes) {
      size =>
      stackTraced {
        val catamorph = newSignalCatamorph
        val cells = for (i <- 0 until size) yield RCell(i)
        for (c <- cells) catamorph += c
  
        def total(n: Int) = n * (n - 1) / 2
        assert(catamorph.signal() == total(cells.length))
        for ((c, i) <- cells.reverse.zipWithIndex) {
          catamorph -= c
          assert(catamorph.signal() == total(cells.length - i - 1))
        }
        true
      }
    }
  
    property(s"$structure: reflect removing and adding") = forAllNoShrink(sizes) {
      max =>
      stackTraced {
        val catamorph = newSignalCatamorph
        val cells = for (i <- 0 until max) yield RCell(i)
        for (c <- cells) catamorph += c
  
        def total(n: Int) = n * (n - 1) / 2
        assert(catamorph.signal() == total(cells.length))
        for ((c, i) <- cells.reverse.take(max / 2).zipWithIndex) {
          catamorph -= c
          assert(catamorph.signal() == total(cells.length - i - 1))
        }
        for (i <- (max - max / 2) until max) {
          catamorph += RCell(i)
          assert(catamorph.signal() == total(i + 1))
        }
        true
      }
    }
  }

}


class SignalCatamorphSpec extends AnyFlatSpec with Matchers {

  plus("Int Monoid", SignalCatamorph(Monoid(0)(_ + _)))

  concat("String Monoid", SignalCatamorph(Monoid("")(_ + _)))

  plus("Int Commute", SignalCatamorph(Commute(0)(_ + _)))

  plus("Int Abelian", SignalCatamorph(Abelian(0)(_ + _)(_ - _)))

  def concat(structure: String, newSignalCatamorph: =>SignalCatamorph[String]) {
    s"A SignalCatamorph using ${structure}s" should "correctly reflect signals" in {
      val catamorph = newSignalCatamorph
      val rc1 = RCell("a")
      val rc2 = RCell("b")
      catamorph += rc1
      catamorph += rc2

      catamorph.signal() should equal ("ab")
    }

    it should "correctly reflect many added signals" in {
      val catamorph = newSignalCatamorph
      val cells = for (i <- 0 until 100) yield new RCell(i + " ")
      for ((c, i) <- cells.zipWithIndex) {
        catamorph += c
        catamorph.signal() should equal ((0 to i).foldLeft("")(_ + _ + " "))
      }
    }

    it should "correctly reflect removing signals" in {
      val catamorph = newSignalCatamorph
      val cells = for (i <- 0 until 50) yield new RCell(i + " ")
      for (c <- cells) catamorph += c
      for ((c, i) <- cells.zipWithIndex; if (i % 2 == 0)) {
        catamorph -= c
        val expected = (0 until 50).filter(x => x % 2 == 1 || x > i)
          .foldLeft("")(_ + _ + " ")
        catamorph.signal() should equal (expected)
      }
    }
  }

  def plus(structure: String, newSignalCatamorph: =>SignalCatamorph[Int]) {
    s"A SignalCatamorph using ${structure}s" should "be empty" in {
      val catamorph = newSignalCatamorph
  
      catamorph.signal() should equal (0)
    }
  
    it should "accurately reflect a single signal" in {
      val catamorph = newSignalCatamorph
      val rc0 = RCell(0)
      catamorph += rc0
  
      catamorph.signal() should equal (0)
      rc0 := 1
      catamorph.signal() should equal (1)
      rc0 := 2
      catamorph.signal() should equal (2)
    }
  
    it should "accurately reflect two signals" in {
      val catamorph = newSignalCatamorph
      val rc0 = RCell(0)
      val rc1 = RCell(0)
      catamorph += rc0
      catamorph += rc1
  
      catamorph.signal() should equal (0)
      rc0 := 1
      catamorph.signal() should equal (1)
      rc1 := 2
      catamorph.signal() should equal (3)
      rc0 := 3
      catamorph.signal() should equal (5)
      rc1 := 20
      catamorph.signal() should equal (23)
      rc0 := -21
      catamorph.signal() should equal (-1)
    }
  
    it should "accurately reflect many signals" in {
      val catamorph = newSignalCatamorph
      val cells = for (_ <- 0 until 20) yield RCell(0)
      for (c <- cells) catamorph += c
  
      catamorph.signal() should equal (0)
      for ((c, i) <- cells.zipWithIndex) c := i
      catamorph.signal() should equal (cells.length * (cells.length - 1) / 2)
      cells(10) := 0
      catamorph.signal() should equal (cells.length * (cells.length - 1) / 2 - 10)
    }
  
    it should "accurately reflect addition of new signals" in {
      val catamorph = newSignalCatamorph
      val cells = for (i <- 0 until 50) yield RCell(i)
      for (c <- cells) catamorph += c
  
      def total(n: Int) = n * (n - 1) / 2
      catamorph.signal() should equal (total(cells.length))
      catamorph += RCell(50)
      catamorph.signal() should equal (total(cells.length + 1))
      catamorph += RCell(51)
      catamorph.signal() should equal (total(cells.length + 2))
      catamorph += RCell(52)
      catamorph.signal() should equal (total(cells.length + 3))
      catamorph += RCell(53)
      catamorph.signal() should equal (total(cells.length + 4))
    }
  
    it should "accurately reflect removal of signals" in {
      val catamorph = newSignalCatamorph
      val cells = for (i <- 0 until 50) yield RCell(i)
      for (c <- cells) catamorph += c
  
      def total(n: Int) = n * (n - 1) / 2
      catamorph.signal() should equal (total(cells.length))
      for ((c, i) <- cells.reverse.zipWithIndex) {
        catamorph -= c
        catamorph.signal() should equal (total(cells.length - i - 1))
      }
    }
  
    it should "accurately reflect signals being removed and added" in {
      val max = 50
      val catamorph = newSignalCatamorph
      val cells = for (i <- 0 until max) yield RCell(i)
      for (c <- cells) catamorph += c
  
      def total(n: Int) = n * (n - 1) / 2
      catamorph.signal() should equal (total(cells.length))
      for ((c, i) <- cells.reverse.take(max / 2).zipWithIndex) {
        catamorph -= c
        catamorph.signal() should equal (total(cells.length - i - 1))
      }
      for (i <- (max - max / 2) until max) {
        catamorph += RCell(i)
        catamorph.signal() should equal (total(i + 1))
      }
    }

  }

}
