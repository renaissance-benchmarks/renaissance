package io.reactors
package container



import org.scalacheck._
import org.scalacheck.Gen._
import org.scalacheck.Prop._
import io.reactors.test._
import scala.collection._



class RContainerCheck extends Properties("RContainer") with ExtendedProperties {

  val sizes = detChoose(0, 500)

  val seeds = detChoose(0, 1000000)

  def randomInts(until: Int) = for (sz <- sizes; seed <- seeds) yield {
    val rng = new scala.util.Random(seed)
    for (i <- 0 until sz) yield rng.nextInt(until)
  }

  property("to") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val emitter = new Events.Emitter[Int]
      val numbers = emitter.to[RHashSet[Int]]
      for (i <- 0 until sz) emitter.react(i)
      val seen = mutable.Buffer[Int]()
      for (x <- numbers) seen += x
      seen.size == sz && seen.toSet == (0 until sz).toSet
    }
  }

  property("count") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      val c0 = numbers.count(_ % 2 == 0)
      assert(c0.get == 0)
      for (i <- 0 until sz) numbers += i
      assert(c0.get == (sz + 1) / 2)
      var last = 0
      c0.onEvent(last = _)
      assert(last == (sz + 1) / 2)
      numbers += sz
      assert(last == sz / 2 + 1)
      numbers -= sz
      last == (sz + 1) / 2
    }
  }

  property("forall") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      val c0 = numbers.forall(_ % 2 == 0)
      assert(c0.get == true)
      for (i <- 0 until sz) numbers += i
      c0.get == (sz <= 1)
    }
  }

  property("exists") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      val c0 = numbers.exists(_ % 2 == 0)
      assert(c0.get == false)
      for (i <- 0 until sz) numbers += i
      c0.get == (sz > 0)
    }
  }

  property("sizes") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      val ss = numbers.sizes
      assert(ss.get == 0)
      val seen = mutable.Buffer[Int]()
      ss.onEvent(seen += _)
      for (i <- 0 until sz) numbers += i
      seen == (0 to sz)
    }
  }

  property("reduce") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      val red = numbers.reduce(0)((s, x) => s + 1)((s, x) => s - 1)
      assert(red.get == 0)
      val seen = mutable.Buffer[Int]()
      red.onEvent(seen += _)
      for (i <- 0 until sz) numbers += i
      for (i <- 0 until sz) numbers -= i
      seen == ((0 to sz) ++ (0 until sz).reverse)
    }
  }

  property("filter") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      val oddSum = numbers.filter(_ % 2 == 0).reduce(0)(_ + _)(_ - _)
      val seen = mutable.Buffer[Int]()
      oddSum.onEvent(seen += _)

      for (i <- 0 until sz) numbers += i
      assert(seen.tail == (2 until sz).filter(_ % 2 == 0).scanLeft(0)(_ + _), seen)
      seen.clear()
      for (i <- 0 until sz) numbers -= i
      val half = (sz + 1) / 2 - 1
      seen == (2 until sz).filter(_ % 2 == 0).scanLeft(half * (half + 1))(_ - _)
    }
  }

  property("to") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      val copied = numbers.to[RHashSet[Int]]

      for (i <- 0 until sz) {
        numbers += i
        assert(copied(i))
      }

      assert(copied.size == sz)

      for (i <- 0 until sz) {
        numbers -= i
        assert(!copied(i))
      }

      copied.size == 0
    }
  }

  property("to with initial elements") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      numbers += 7
      val copied = numbers.to[RHashSet[Int]]

      assert(copied.size == 1)
      assert(copied(7))

      numbers += 11
      assert(copied.size == 2)
      assert(copied(11))

      true
    }
  }

  property("map") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      val longs = numbers.map(_.toLong).to[RHashSet[Long]]

      for (i <- 0 until sz) {
        numbers += i
        assert(longs(i.toLong))
      }

      assert(longs.size == sz)

      for (i <- 0 until sz) {
        numbers -= i
        assert(!longs(i.toLong))
      }

      longs.size == 0
    }
  }

  property("map to Double") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      val doubles = numbers.map(_.toDouble).to[RHashSet[Double]]

      for (i <- 0 until sz) {
        numbers += i
        assert(doubles(i.toDouble))
      }

      true
    }
  }

  def testUnionPrimitives(sz: Int): Prop = {
    val xs = new RHashSet[Int]
    val ys = new RHashSet[Int]
    val both = (xs union ys).to[RHashSet[Int]]
    def check(nums: Int*) {
      for (n <- nums)
        assert(both(n) == true, s"(not true for $n in ${nums.mkString(", ")})")
    }

    xs += 1
    check(1)
    ys += 1
    check(1)
    xs -= 1
    check(1)
    ys -= 1
    check()

    for (i <- 0 until sz) {
      if (i % 2 == 0) xs += i
      else ys += i
      if (i % 10 == 0) check((0 to i): _*)
    }
    check((0 until sz): _*)

    for (i <- 0 until sz) {
      if (i % 2 == 0) ys += i
      else xs += i
    }
    check((0 until sz): _*)

    for (i <- 0 until sz) {
      if (i % 2 == 0) xs -= i
      else ys -= i
    }
    check((0 until sz): _*)

    for (i <- 0 until sz) {
      if (i % 2 == 0) ys -= i
      else xs -= i
      if (i % 10 == 0) check((i + 1) until sz: _*)
    }
    for (i <- 0 until sz) assert(!both(i))

    true
  }

  property("union primitives") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      testUnionPrimitives(sz)
    }
  }

  def testUnionReferences(sz: Int): Prop = {
    val xs = new RHashSet[String]
    val ys = new RHashSet[String]
    val both = (xs union ys).to[RHashSet[String]]
    def check(nums: String*) {
      for (n <- nums)
        assert(both(n) == true, s"(not true for $n in ${nums.mkString(", ")})")
    }
    val inputs = (0 until sz).map(_.toString)

    xs += "1"
    check("1")
    ys += "1"
    check("1")
    xs -= "1"
    check("1")
    ys -= "1"
    check()

    for (i <- 0 until sz) {
      if (i % 2 == 0) xs += inputs(i)
      else ys += inputs(i)
    }
    check(inputs: _*)

    for (i <- 0 until sz) {
      if (i % 2 == 0) ys += inputs(i)
      else xs += inputs(i)
    }
    check(inputs: _*)

    for (i <- 0 until sz) {
      if (i % 2 == 0) xs -= inputs(i)
      else ys -= inputs(i)
    }
    check(inputs: _*)

    for (i <- 0 until sz) {
      if (i % 2 == 0) ys -= inputs(i)
      else xs -= inputs(i)
    }
    for (i <- 0 until sz) assert(!both(inputs(i)))

    true
  }

  property("union references") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      testUnionReferences(sz)
    }
  }

  property("fold") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = new RHashSet[Int]
      numbers += 1
      val sum = numbers.toAggregate(0)(_ + _)

      assert(sum() == 1)

      for (n <- 2 until sz) {
        numbers += n
        assert(sum() == n * (n + 1) / 2)
      }
      true
    }
  }

  property("commutative fold") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = new RHashSet[Set[Int]]
      val union = numbers.toCommuteAggregate(Set())(_ ++ _)

      assert(union() == Set())

      for (n <- 1 until sz) {
        numbers += Set(n)
        assert(union() == Set() ++ (1 to n))
      }
      true
    }
  }

  property("update the size") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val numbers = RHashSet[Int]
      numbers += 0
      val size = numbers.sizes.toEmpty

      for (i <- 1 to sz) {
        numbers += i
        assert(size() == i + 1, s"i == $i, size() == ${size()}")
      }
      true
    }
  }

  property("collect") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val table = new RHashMap[Int, String]
      val oks = table.pairs.collect({
        case (k, "ok") => (k, "ok")
      })
      val observed = mutable.Buffer[String]()
      val insertSub = oks.inserts.onEvent(kv => observed += kv._2)
      for (i <- 0 until sz) table(i) = if (i % 2 == 0) "ok" else "notok"
  
      assert(observed.size == (sz + 1) / 2, s"sz = $sz, size = ${observed.size}")
      for (v <- observed) assert(v == "ok")
      true
    }
  }


  property("be eagerly evaluated") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val set = new RHashSet[Int]
      for (i <- 0 until sz) set += i
      val mapped = set.map(_ + 1).to[RHashSet[Int]]

      assert(mapped.size == sz)
      for (x <- mapped) assert(set(x / 2) == true)
      true
    }
  }

}
