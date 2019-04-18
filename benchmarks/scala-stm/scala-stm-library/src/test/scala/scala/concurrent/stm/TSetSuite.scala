/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite
import scala.util.Random
import scala.collection.mutable

class TSetSuite extends FunSuite {

  test("number equality trickiness") {
    assert(TSet(10L).single contains 10)
    //assert(TSet(10).single contains 10L)
    assert(TSet[Number](10L).single contains 10)
    assert(TSet[Number](10).single contains 10L)
    assert(TSet[Any](10L).single contains 10)
    assert(TSet[Any](10).single contains 10L)
    assert(TSet[AnyRef](10L.asInstanceOf[AnyRef]).single contains 10.asInstanceOf[AnyRef])
    assert(TSet[AnyRef](10.asInstanceOf[AnyRef]).single contains 10L.asInstanceOf[AnyRef])
  }

  test("character equality trickiness") {
    assert(TSet('*').single contains 42)
    assert(TSet(42: Byte).single contains '*')
    assert(TSet[Any]('*').single contains (42: Short))
    assert(TSet[Any](42L).single contains '*')
    assert(TSet[AnyRef]('*'.asInstanceOf[AnyRef]).single contains 42.0.asInstanceOf[AnyRef])
    assert(TSet[AnyRef](42.0f.asInstanceOf[AnyRef]).single contains '*'.asInstanceOf[AnyRef])
  }

  case class BadHash(k: Int) {
    override def hashCode = if (k > 500) k / 5 else 0
  }

  test("correct despite poor hash function") {
    val mut = TSet(((0 until 1000) map { i => BadHash(i) }): _*).single
    for (i <- -500 until 1500)
      assert(mut(BadHash(i)) === (i >= 0 && i < 1000))
  }

  test("clone captures correct atomic writes") {
    val mut = TSet((0 until 100): _*)
    val z = atomic { implicit txn =>
      mut ++= (100 until 200)
      val z = mut.clone.single
      mut ++= (200 until 300)
      z
    }
    assert(z.size === 200)
    for (i <- 0 until 200)
      assert(z.contains(i))
  }

  test("clone doesn't include discarded writes") {
    val mut = TSet((0 until 100): _*)
    val z = atomic { implicit txn =>
      atomic { implicit txn =>
        mut ++= (100 until 200)
        if ("likely".## != 0)
          retry
      } orAtomic { implicit txn =>
        mut ++= (200 until 300)
      }
      val z = mut.clone.single
      atomic { implicit txn =>
        mut ++= (300 until 400)
        if ("likely".## != 0)
          retry
      } orAtomic { implicit txn =>
        mut ++= (400 until 500)
      }
      z
    }
    assert(z.size === 200)
    for (i <- 0 until 100)
      assert(z.contains(i))
    for (i <- 200 until 300)
      assert(z.contains(i))
  }

  test("clone is transactional") {
    val mut = TSet((0 until 100): _*)
    val z = atomic { implicit txn =>
      atomic { implicit txn =>
        mut ++= (100 until 105)
        if ("likely".## != 0)
          retry
      } orAtomic { implicit txn =>
        mut ++= (200 until 205)
      }
      val z = mut.clone.single
      atomic { implicit txn =>
        z ++= (300 until 305)
        if ("likely".## != 0)
          retry
      } orAtomic { implicit txn =>
        z ++= (400 until 405)
      }
      z
    }
    assert(z.size === 110)
    for (i <- 0 until 100)
      assert(z.contains(i))
    for (i <- 200 until 205)
      assert(z.contains(i))
    for (i <- 400 until 405)
      assert(z.contains(i))
  }


  test("random sequential") {
    randomTest(1500)
  }

  test("more random sequential", Slow) {
    randomTest(30000)
  }

  def randomTest(total: Int) {
    val rand = new Random()

    def nextKey(): String = "key" + (rand.nextInt() >>> rand.nextInt())

    var mut = TSet.empty[String].single
    val base = mutable.Set.empty[String]

    for (i <- 0 until total) {
      val pct = rand.nextInt(250)
      val k = nextKey
      if (pct < 15) {
        assert(base.contains(k) === mut.contains(k))
      } else if (pct < 20) {
        assert(base(k) === mut(k))
      } else if (pct < 35) {
        assert(base.add(k) === mut.add(k))
      } else if (pct < 40) {
        val v = rand.nextBoolean
        base(k) = v
        mut(k) = v
      } else if (pct < 55) {
        assert(base.remove(k) === mut.remove(k))
      } else if (pct < 60) {
        for (j <- 0 until (i / (total / 20))) {
          if (!base.isEmpty) {
            val k1 = base.iterator.next
            assert(base.remove(k1) === mut.remove(k1))
          }
        }
      } else if (pct < 63) {
        mut = mut.clone
      } else if (pct < 66) {
        assert(base.toSet === mut.snapshot)
      } else if (pct < 69) {
        assert(base.isEmpty === mut.isEmpty)
      } else if (pct < 72) {
        assert(base.size === mut.size)
      } else if (pct < 77) {
        assert(base eq (base += k))
        assert(mut eq (mut += k))
      } else if (pct < 80) {
        val k2 = nextKey
        val k3 = nextKey
        assert(base eq (base += (k, k2, k3)))
        assert(mut eq (mut += (k, k2, k3)))
      } else if (pct < 83) {
        val k2 = nextKey
        val k3 = nextKey
        assert(base eq (base ++= Array(k, k2, k3)))
        assert(mut eq (mut ++= Array(k, k2, k3)))
      } else if (pct < 82) {
        assert(mut eq (mut ++= Nil))
      } else if (pct < 88) {
        assert(base eq (base -= k))
        assert(mut eq (mut -= k))
      } else if (pct < 91) {
        val k2 = nextKey
        val k3 = nextKey
        assert(base eq (base -= (k, k2, k3)))
        assert(mut eq (mut -= (k, k2, k3)))
      } else if (pct < 93) {
        val k2 = nextKey
        val k3 = nextKey
        assert(base eq (base --= Array(k, k2, k3)))
        assert(mut eq (mut --= Array(k, k2, k3)))
      } else if (pct < 94) {
        assert(mut eq (mut --= Nil))
      } else if (pct < 95) {
        mut = TSet(mut.toArray: _*).single
      } else if (pct < 96) {
        mut = TSet.empty[String].single ++= mut
      } else if (pct < 97) {
        val s2 = mutable.Set.empty[String]
        for (k <- mut) { s2 += k }
        assert(base === s2)
      } else if (pct < 98) {
        val s2 = mutable.Set.empty[String]
        for (k <- mut.iterator) { s2 += k }
        assert(base === s2)
      } else if (pct < 115) {
        assert(base.contains(k) === atomic { implicit txn => mut.tset.contains(k) })
      } else if (pct < 120) {
        assert(base(k) === atomic { implicit txn => mut.tset(k) })
      } else if (pct < 135) {
        assert(base.add(k) === atomic { implicit txn => mut.tset.add(k) })
      } else if (pct < 140) {
        val v = rand.nextBoolean
        base(k) = v
        atomic { implicit txn => mut.tset(k) = v }
      } else if (pct < 155) {
        assert(base.remove(k) === atomic { implicit txn => mut.tset.remove(k) })
      } else if (pct < 160) {
        for (j <- 0 until (i / (total / 20))) {
          if (!base.isEmpty) {
            val k1 = base.iterator.next
            assert(base.remove(k1) === atomic { implicit txn => mut.tset.remove(k1) })
          }
        }
      } else if (pct < 163) {
        mut = atomic { implicit txn => mut.tset.clone.single }
      } else if (pct < 166) {
        assert(base.toSet === atomic { implicit txn => mut.tset.snapshot })
      } else if (pct < 169) {
        assert(base.isEmpty === atomic { implicit txn => mut.tset.isEmpty })
      } else if (pct < 172) {
        assert(base.size === atomic { implicit txn => mut.tset.size })
      } else if (pct < 177) {
        assert(base eq (base += k))
        assert(mut.tset eq atomic { implicit txn => mut.tset += k })
      } else if (pct < 180) {
        val k2 = nextKey
        val k3 = nextKey
        assert(base eq (base += (k, k2, k3)))
        assert(mut.tset eq atomic { implicit txn => mut.tset += (k, k2, k3) })
      } else if (pct < 182) {
        val k2 = nextKey
        val k3 = nextKey
        assert(base eq (base ++= Array(k, k2, k3)))
        assert(mut.tset eq atomic { implicit txn => mut.tset ++= Array(k, k2, k3) })
      } else if (pct < 183) {
        assert(mut.tset eq atomic { implicit txn => mut.tset ++= Nil })
      } else if (pct < 188) {
        assert(base eq (base -= k))
        assert(mut.tset eq atomic { implicit txn => mut.tset -= k })
      } else if (pct < 191) {
        val k2 = nextKey
        val k3 = nextKey
        assert(base eq (base -= (k, k2, k3)))
        assert(mut.tset eq atomic { implicit txn => mut.tset -= (k, k2, k3) })
      } else if (pct < 193) {
        val k2 = nextKey
        val k3 = nextKey
        assert(base eq (base --= Array(k, k2, k3)))
        assert(mut.tset eq atomic { implicit txn => mut.tset --= Array(k, k2, k3) })
      } else if (pct < 194) {
        assert(mut.tset eq atomic { implicit txn => mut.tset --= Nil })
      } else if (pct < 195) {
        mut = atomic { implicit txn => TSet(mut.tset.toArray: _*).single }
      } else if (pct < 196) {
        mut = atomic { implicit txn => TSet.empty[String] ++= mut.tset }.single
      } else if (pct < 197) {
        atomic { implicit txn =>
          val s2 = mutable.Set.empty[String]
          for (k <- mut.tset) { s2 += k }
          assert(base === s2)
        }
      } else if (pct < 198) {
        atomic { implicit txn =>
          val s2 = mutable.Set.empty[String]
          for (k <- mut.tset.iterator) { s2 += k }
          assert(base === s2)
        }
      } else if (pct < 200) {
        var b = base.toSet
        var s = mut.snapshot
        assert(b.iterator.toSet === s.iterator.toSet)
        while (!b.isEmpty) {
          if (rand.nextInt(100) < 75) {
            val k = b.iterator.next
            assert(b(k) === s(k))
            b -= k
            s -= k
            assert(b.size === s.size)
          } else {
            val k = nextKey
            b += k
            s += k
          }
        }
        assert(b.isEmpty === s.isEmpty)
        val k = nextKey
        b += k
        s += k
        assert(b === s)
      } else if (pct < 208) {
        val cutoff = nextKey
        base.retain { v => v < cutoff }
        mut.retain { v => v < cutoff }
      } else if (pct < 211) {
        val cutoff = nextKey
        base.retain { v => v < cutoff }
        atomic { implicit txn => mut.tset.retain { v => v < cutoff } }
      } else if (pct < 214) {
        val b2 = base map { v => v.substring(3).toInt }
        val m2 = mut map { v => v.substring(3).toInt }
        assert(b2 === m2)
        assert(m2 eq m2.tset.single)
        mut = m2 map { v => "key" + v }
      } else if (pct < 217) {
        mut = TSet.View.empty[String] ++ mut
      } else if (pct < 219) {
        mut = atomic { implicit txn => mut.tset.empty ++ mut.tset }
      } else if (pct < 221) {
        val b = TSet.View.newBuilder[String]
        b ++= mut
        b.clear()
        b ++= mut
        mut = b.result
      } else if (pct < 223) {
        mut = (atomic { implicit txn =>
          val b = TSet.newBuilder[String]
          b ++= mut.tset
          b.clear()
          b ++= mut.tset
          b.result
        }).single
      }
    }
  }

  test("tset clear") {
    val s = TSet(1, 2)
    atomic { implicit txn => s.clear() }
    assert(s.single.isEmpty)
    assert(s.single.size === 0)
    assert(!s.single.iterator.hasNext)
    for (e <- s.single) { assert(false) }
  }

  test("view clear") {
    val s = TSet(1, 2)
    s.single.clear()
    assert(s.single.size === 0)
    assert(!s.single.iterator.hasNext)
    for (e <- s.single) { assert(false) }
  }

  test("null entry") {
    val s = TSet("abc", "def", (null: AnyRef))
    assert(s.single.size === 3)
    assert(s.single(null))
    assert(s.single.remove(null))
    assert(s.single.size === 2)
    assert(!s.single(null))
    assert(s.single.add(null))
    assert(s.single.size === 3)
  }

  test("view builder magic") {
    val s0 = TSet.View(1, 2, 3)
    val s1 = s0 map { "x" + _ }
    val s2: TSet.View[String] = s1
    assert(s1 === Set("x1", "x2", "x3"))
  }

  test("iterator crossing a txn boundary") {
    val ks = (0 until 100) map { i => "x" + (i % 37) }
    val s = TSet(ks: _*)
    val iter = atomic { implicit txn => s.iterator }
    assert(iter.toSet === ks.toSet)
  }

  test("iterator after many removes") {
    val s = TSet.View.empty[Int]
    for (i <- 0 until 100000)
      s += i
    for (i <- 0 until 100000)
      s -= i
    assert(!s.iterator.hasNext)
    for (e <- s) { assert(false) }
    atomic { implicit txn => assert(s.tset.isEmpty) }
    atomic { implicit txn => assert(s.tset.size === 0) }
    assert(s.isEmpty)
    assert(s.size === 0)
  }

  test("view snapshot foreach") {
    val ks = (0 until 100)
    val s = TSet(ks: _*)
    var n = 0
    for (k <- s.single.snapshot) n += k
    assert(n === 4950)
  }

  test("txn snapshot foreach") {
    val ks = (0 until 100)
    val s = TSet(ks: _*)
    var n = 0
    for (k <- atomic { implicit txn => s.snapshot }) n += k
    assert(n === 4950)
  }

  test("TxnDebuggable") {
    val s1 = TSet[Int]()
    val s2 = TSet(1)
    val s3 = TSet(1, 2).single
    val s4 = TSet((0 until 10000): _*).single

    assert(s1.dbgStr === "TSet[size=0]()")
    assert(s2.dbgStr === "TSet[size=1](1)")
    assert(s3.dbgStr == "TSet[size=2](1, 2)" ||
           s3.dbgStr == "TSet[size=2](2, 1)")
    assert(s4.dbgStr.startsWith("TSet[size=10000]("))
    assert(s4.dbgStr.length >= 1000)
    assert(s4.dbgStr.length < 1100)

    assert(s1.dbgValue.asInstanceOf[Array[_]].length === 0)
    assert(s2.dbgValue.asInstanceOf[Array[_]].length === 1)
    assert(s3.dbgValue.asInstanceOf[Array[_]].length === 2)
    assert(s4.dbgValue.asInstanceOf[Array[_]].length === 10000)
  }
}
