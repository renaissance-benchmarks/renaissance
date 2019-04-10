/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite
import scala.util.Random
import scala.collection.mutable
import skel.SimpleRandom

class TMapSuite extends FunSuite {

  private def value(k: Int) = "x" + k
  private def kvRange(b: Int, e: Int) = (b until e) map { i => (i -> value(i)) }

  test("number equality trickiness") {
    assert(TMap(10L -> "").single contains 10)
    //assert(TMap(10 -> "").single contains 10L)
    assert(TMap[Number, String]((10L: Number) -> "").single contains 10)
    assert(TMap[Number, String]((10: Number) -> "").single contains 10L)
    assert(TMap[Any, String](10L -> "").single contains 10)
    assert(TMap[Any, String](10 -> "").single contains 10L)
    assert(TMap[AnyRef, String](10L.asInstanceOf[AnyRef] -> "").single contains 10.asInstanceOf[AnyRef])
    assert(TMap[AnyRef, String](10.asInstanceOf[AnyRef] -> "").single contains 10L.asInstanceOf[AnyRef])
  }

  test("character equality trickiness") {
    assert(TMap('*' -> "").single contains 42)
    assert(TMap((42: Byte) -> "").single contains '*')
    assert(TMap[Any, String]('*' -> "").single contains (42: Short))
    assert(TMap[Any, String](42L -> "").single contains '*')
    assert(TMap[AnyRef, String]('*'.asInstanceOf[AnyRef] -> "").single contains 42.0.asInstanceOf[AnyRef])
    assert(TMap[AnyRef, String](42.0f.asInstanceOf[AnyRef] -> "").single contains '*'.asInstanceOf[AnyRef])
  }

  case class BadHash(k: Int) {
    override def hashCode = if (k > 500) k / 5 else 0
  }

  test("correct despite poor hash function") {
    val mut = TMap(((0 until 1000) map { i => (BadHash(i) -> i) }): _*).single
    for (i <- -500 until 1500)
      assert(mut.get(BadHash(i)) === (if (i >= 0 && i < 1000) Some(i) else None))
  }

  test("clone captures correct atomic writes") {
    val mut = TMap(kvRange(0, 100): _*)
    val z = atomic { implicit txn =>
      mut ++= kvRange(100, 200)
      val z = mut.clone.single
      mut ++= kvRange(200, 300)
      z
    }
    assert(z.size === 200)
    for (i <- 0 until 200)
      assert(z(i) === value(i))
  }

  test("clone doesn't include discarded writes") {
    val mut = TMap(kvRange(0, 100): _*)
    val z = atomic { implicit txn =>
      atomic { implicit txn =>
        mut ++= kvRange(100, 200)
        if ("likely".## != 0)
          retry
      } orAtomic { implicit txn =>
        mut ++= kvRange(200, 300)
      }
      val z = mut.clone.single
      atomic { implicit txn =>
        mut ++= kvRange(300, 400)
        if ("likely".## != 0)
          retry
      } orAtomic { implicit txn =>
        mut ++= kvRange(400, 500)
      }
      z
    }
    assert(z.size === 200)
    for (i <- 0 until 100)
      assert(z(i) === value(i))
    for (i <- 200 until 300)
      assert(z(i) === value(i))
  }

  test("clone is transactional") {
    val mut = TMap(kvRange(0, 100): _*)
    val z = atomic { implicit txn =>
      atomic { implicit txn =>
        mut ++= kvRange(100, 105)
        if ("likely".## != 0)
          retry
      } orAtomic { implicit txn =>
        mut ++= kvRange(200, 205)
      }
      val z = mut.clone.single
      atomic { implicit txn =>
        z ++= kvRange(300, 305)
        if ("likely".## != 0)
          retry
      } orAtomic { implicit txn =>
        z ++= kvRange(400, 405)
      }
      z
    }
    assert(z.size === 110)
    for (i <- 0 until 100)
      assert(z(i) === value(i))
    for (i <- 200 until 205)
      assert(z(i) === value(i))
    for (i <- 400 until 405)
      assert(z(i) === value(i))
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
    def nextValue(): Int = if (rand.nextInt(10) == 0) 0 else rand.nextInt()

    var mut = TMap.empty[String, Int].single
    val base = mutable.Map.empty[String, Int]

    for (i <- 0 until total) {
      val pct = rand.nextInt(250)
      val k = nextKey()
      val v = nextValue()
      if (pct < 15) {
        assert(base.get(k) === mut.get(k))
      } else if (pct < 20) {
        val a = try { Some(base(k)) } catch { case _: NoSuchElementException => None }
        val b = try { Some(mut(k)) } catch { case _: NoSuchElementException => None }
        assert(a === b)
      } else if (pct < 35) {
        assert(base.put(k, v) === mut.put(k, v))
      } else if (pct < 40) {
        base(k) = v
        mut(k) = v
      } else if (pct < 45) {
        assert(base.contains(k) === mut.contains(k))
      } else if (pct < 55) {
        assert(base.remove(k) === mut.remove(k))
      } else if (pct < 60) {
        for (j <- 0 until (i / (total / 20))) {
          if (!base.isEmpty) {
            val k1 = base.iterator.next()._1
            assert(base.remove(k1) === mut.remove(k1))
          }
        }
      } else if (pct < 63) {
        mut = mut.clone
      } else if (pct < 66) {
        assert(base.toMap === mut.snapshot)
      } else if (pct < 69) {
        assert(base.isEmpty === mut.isEmpty)
      } else if (pct < 72) {
        assert(base.size === mut.size)
      } else if (pct < 77) {
        assert(base eq (base += (k -> v)))
        assert(mut eq (mut += (k -> v)))
      } else if (pct < 80) {
        val kv2 = (nextKey -> nextValue)
        val kv3 = (nextKey -> nextValue)
        assert(base eq (base += ((k -> v), kv2, kv3)))
        assert(mut eq (mut += ((k -> v), kv2, kv3)))
      } else if (pct < 82) {
        val kv2 = (nextKey -> nextValue)
        val kv3 = (nextKey -> nextValue)
        assert(base eq (base ++= Array((k -> v), kv2, kv3)))
        assert(mut eq (mut ++= Array((k -> v), kv2, kv3)))
      } else if (pct < 83) {
        assert(mut eq (mut ++= Nil))
      } else if (pct < 88) {
        assert(base eq (base -= k))
        assert(mut eq (mut -= k))
      } else if (pct < 91) {
        val k2 = nextKey()
        val k3 = nextKey()
        assert(base eq (base -= (k, k2, k3)))
        assert(mut eq (mut -= (k, k2, k3)))
      } else if (pct < 93) {
        val k2 = nextKey()
        val k3 = nextKey()
        assert(base eq (base --= Array(k, k2, k3)))
        assert(mut eq (mut --= Array(k, k2, k3)))
      } else if (pct < 94) {
        assert(mut eq (mut --= Nil))
      } else if (pct < 95) {
        mut = TMap(mut.toArray: _*).single
      } else if (pct < 96) {
        mut = TMap.empty[String, Int].single ++= mut
      } else if (pct < 97) {
        val m2 = mutable.Map.empty[String, Int]
        for (kv <- mut) { m2 += kv }
        assert(base === m2)
      } else if (pct < 98) {
        val m2 = mutable.Map.empty[String, Int]
        for (kv <- mut.iterator) { m2 += kv }
        assert(base === m2)
      } else if (pct < 115) {
        assert(base.get(k) === atomic { implicit t => mut.tmap.get(k) })
      } else if (pct < 120) {
        val a = try { Some(base(k)) } catch { case _: NoSuchElementException => None }
        val b = try { Some(atomic { implicit t => mut.tmap(k) }) } catch { case _: NoSuchElementException => None }
        assert(a === b)
      } else if (pct < 135) {
        assert(base.put(k, v) === atomic { implicit t => mut.tmap.put(k, v) })
      } else if (pct < 140) {
        base(k) = v
        atomic { implicit t => mut.tmap(k) = v }
      } else if (pct < 145) {
        assert(base.contains(k) === atomic { implicit t => mut.tmap.contains(k) })
      } else if (pct < 155) {
        assert(base.remove(k) === atomic { implicit t => mut.tmap.remove(k) })
      } else if (pct < 160) {
        for (j <- 0 until (i / (total / 20))) {
          if (!base.isEmpty) {
            val k1 = base.iterator.next()._1
            assert(base.remove(k1) === atomic { implicit t => mut.tmap.remove(k1) })
          }
        }
      } else if (pct < 163) {
        mut = atomic { implicit t => mut.tmap.clone.single }
      } else if (pct < 166) {
        assert(base.toMap === atomic { implicit t => mut.tmap.snapshot })
      } else if (pct < 169) {
        assert(base.isEmpty === atomic { implicit t => mut.tmap.isEmpty })
      } else if (pct < 172) {
        assert(base.size === atomic { implicit t => mut.tmap.size })
      } else if (pct < 177) {
        assert(base eq (base += (k -> v)))
        assert(mut.tmap eq atomic { implicit t => mut.tmap += (k -> v) })
      } else if (pct < 180) {
        val kv2 = (nextKey -> nextValue)
        val kv3 = (nextKey -> nextValue)
        assert(base eq (base += ((k -> v), kv2, kv3)))
        assert(mut.tmap eq atomic { implicit t => mut.tmap += ((k -> v), kv2, kv3) })
      } else if (pct < 182) {
        val kv2 = (nextKey -> nextValue)
        val kv3 = (nextKey -> nextValue)
        assert(base eq (base ++= Array((k -> v), kv2, kv3)))
        assert(mut.tmap eq atomic { implicit t => mut.tmap ++= Array((k -> v), kv2, kv3) })
      } else if (pct < 183) {
        assert(mut.tmap eq atomic { implicit t => mut.tmap ++= Nil })
      } else if (pct < 188) {
        assert(base eq (base -= k))
        assert(mut.tmap eq atomic { implicit t => mut.tmap -= k })
      } else if (pct < 191) {
        val k2 = nextKey()
        val k3 = nextKey()
        assert(base eq (base -= (k, k2, k3)))
        assert(mut.tmap eq atomic { implicit t => mut.tmap -= (k, k2, k3) })
      } else if (pct < 193) {
        val k2 = nextKey()
        val k3 = nextKey()
        assert(base eq (base --= Array(k, k2, k3)))
        assert(mut.tmap eq atomic { implicit t => mut.tmap --= Array(k, k2, k3) })
      } else if (pct < 194) {
        assert(mut.tmap eq atomic { implicit t => mut.tmap --= Nil })
      } else if (pct < 195) {
        mut = atomic { implicit t => TMap(mut.tmap.toArray: _*).single }
      } else if (pct < 196) {
        mut = atomic { implicit t => TMap.empty[String, Int] ++= mut.tmap }.single
      } else if (pct < 197) {
        atomic { implicit t =>
          val m2 = mutable.Map.empty[String, Int]
          for (kv <- mut.tmap) { m2 += kv }
          assert(base === m2)
        }
      } else if (pct < 198) {
        atomic { implicit t =>
          val m2 = mutable.Map.empty[String, Int]
          for (kv <- mut.tmap.iterator) { m2 += kv }
          assert(base === m2)
        }
      } else if (pct < 200) {
        var b = base.toMap
        var s = mut.snapshot
        assert(b.iterator.toMap === s.iterator.toMap)
        while (!b.isEmpty) {
          if (rand.nextInt(100) < 75) {
            val k = b.keysIterator.next()
            assert(b(k) === s(k))
            b -= k
            s -= k
            assert(b.size === s.size)
          } else {
            val kv = (nextKey -> nextValue)
            b += kv
            s += kv
          }
        }
        assert(b.isEmpty === s.isEmpty)
        val kv = (nextKey -> nextValue)
        b += kv
        s += kv
        assert(b === s)
      } else if (pct < 208) {
        val cutoff = rand.nextInt()
        assert(base eq (base.retain { (k, v) => v < cutoff }))
        assert(mut eq (mut.retain { (k, v) => v < cutoff }))
      } else if (pct < 211) {
        val cutoff = rand.nextInt()
        assert(base eq (base.retain { (k, v) => v < cutoff }))
        assert(mut.tmap eq atomic { implicit txn => mut.tmap.retain { (k, v) => v < cutoff } })
      } else if (pct < 214) {
        val k = nextKey()
        val v = nextValue()
        var bf = false
        var mf = false
        assert(base.getOrElseUpdate(k, { bf = true ; v }) === mut.getOrElseUpdate(k, { mf = true ; v }))
        assert(bf === mf)
      } else if (pct < 217) {
        val k = nextKey()
        val v = nextValue()
        var bf = false
        var mf = false
        assert(base.getOrElseUpdate(k, { bf = true ; v }) === atomic { implicit txn => mut.getOrElseUpdate(k, { mf = true ; v }) })
        assert(bf === mf)
      } else if (pct < 220) {
        assert(base eq (base.transform { (k, v) => v + 1 }))
        assert(mut eq (mut.transform { (k, v) => v + 1 }))
      } else if (pct < 223) {
        assert(base eq (base.transform { (k, v) => v + 1 }))
        assert(mut.tmap eq atomic { implicit txn => mut.tmap.transform { (k, v) => v + 1 } })
      } else if (pct < 225) {
        val b2 = base map { kv => (kv._1 -> kv._2 * 1L) }
        val m2 = mut map { kv => (kv._1 -> kv._2 * 1L) }
        assert(b2 === m2)
        assert(m2 eq m2.tmap.single)
        mut = m2 map { kv => (kv._1 -> kv._2.asInstanceOf[Int]) }
      } else if (pct < 227) {
        mut = TMap.View.empty[String, Int] ++ mut
      } else if (pct < 229) {
        mut = atomic { implicit txn => mut.tmap.empty ++ mut.tmap }
      } else if (pct < 231) {
        val b = TMap.View.newBuilder[String, Int]
        b ++= mut
        b.clear()
        b ++= mut
        mut = b.result()
      } else if (pct < 233) {
        mut = (atomic { implicit txn =>
          val b = TMap.newBuilder[String, Int]
          b ++= mut.tmap
          b.clear()
          b ++= mut.tmap
          b.result()
        }).single
      }
    }
  }

  test("tmap clear") {
    val m = TMap(1 -> "one", 2 -> "two")
    atomic { implicit txn => m.clear() }
    assert(m.single.size === 0)
    assert(!m.single.iterator.hasNext)
    for (e <- m.single) { assert(false) }
  }
  
  test("view clear") {
    val m = TMap(1 -> "one", 2 -> "two")
    m.single.clear()
    assert(m.single.size === 0)
    assert(!m.single.iterator.hasNext)
    for (e <- m.single) { assert(false) }
  }

  test("null key") {
    val m = TMap((null : AnyRef) -> "abc", "def" -> "ghi")
    assert(m.single.size === 2)
    assert(m.single(null) === "abc")
    assert(m.single.remove(null) === Some("abc"))
    assert(m.single.size === 1)
    assert(m.single.put(null, "jkl") === None)
    assert(m.single.size === 2)
    assert(m.single.get(null) === Some("jkl"))
  }

  test("null value") {
    val m = TMap("abc" -> null, "def" -> "ghi")
    assert(m.single.size === 2)
    assert(m.single.get("abc") === Some(null))
    assert(m.single.remove("abc") === Some(null))
    assert(m.single.size === 1)
    assert(m.single.put("jkl", null) === None)
    assert(m.single.size === 2)
    assert(m.single.contains("jkl"))
  }

  test("view builder magic") {
    val fwd = TMap.View(1 -> "one", 2 -> "two")
    val rev = fwd map { kv => (kv._2 -> kv._1) }
    val rev2: TMap.View[String, Int] = rev
    assert(rev === Map("one" -> 1, "two" -> 2))
  }

  test("iterator crossing a txn boundary") {
    val kvs = (0 until 100) map { i => ((i % 37) -> ("x" + i)) }
    val m = TMap(kvs: _*)
    val iter = atomic { implicit txn => m.iterator }
    assert(iter.toMap === kvs.toMap)
  }

  test("iterator after many removes") {
    val m = TMap.View.empty[Int, Int]
    for (i <- 0 until 100000)
      m(i) = i
    for (i <- 0 until 100000)
      m -= i
    assert(!m.iterator.hasNext)
    for (e <- m) { assert(false) }
    atomic { implicit txn => assert(m.tmap.isEmpty) }
    atomic { implicit txn => assert(m.tmap.size === 0) }
    assert(m.isEmpty)
    assert(m.size === 0)
  }

  test("view snapshot foreach") {
    val kvs = (0 until 100) map { i => (i -> ("x" + (i % 37))) }
    val m = TMap(kvs: _*)
    var n = 0
    for ((k, v) <- m.single.snapshot) n += k
    assert(n === 4950)
  }

  test("txn snapshot foreach") {
    val kvs = (0 until 100) map { i => (i -> ("x" + (i % 37))) }
    val m = TMap(kvs: _*)
    var n = 0
    for ((k, v) <- atomic { implicit txn => m.snapshot }) n += k
    assert(n === 4950)
  }

  test("contention") {
    val values = (0 until 37) map { i => "foo" + i }
    for (pass <- 0 until 2) {
      val numThreads = 8
      val m = TMap.empty[Int, String]
      val threads = for (t <- 0 until numThreads) yield new Thread {
        override def run() {
          var rand = new SimpleRandom(t)
          var i = 0
          while (i < 1000000) {
            if (rand.nextInt(2) == 0) {
              var j = 0
              while (j < 64) {
                val key = rand.nextInt(1 << 11)
                val pct = rand.nextInt(100)
                if (pct < 33)
                  m.single.contains(key)
                else if (pct < 33)
                  m.single.put(key, values(rand.nextInt(values.length)))
                else
                  m.single.remove(key)
                j += 1
              }
            } else {
              rand = atomic { implicit txn =>
                val r = rand.clone
                var j = 0
                while (j < 64) {
                  val key = r.nextInt(1 << 11)
                  val pct = r.nextInt(100)
                  if (pct < 33)
                    m.contains(key)
                  else if (pct < 33)
                    m.put(key, values(r.nextInt(values.length)))
                  else
                    m.remove(key)
                  j += 1
                }
                r
              }
            }
            i += 64
          }
        }
      }

      val begin = System.currentTimeMillis
      for (t <- threads) t.start()
      for (t <- threads) t.join()
      val elapsed = System.currentTimeMillis - begin

      println("TMap: contended: " + numThreads + " threads, total throughput was " + (elapsed / numThreads) + " nanos/op")
    }
  }

  test("atomicity violation") {
    // This test makes sure that the copy-on-write snapshot mechanism can't
    // expose the intermediate state of a txn to a non-txn get.
    val m = TMap(kvRange(0, 1000): _*).single
    m(0) = "okay"
    val failed = Ref(-1).single
    val threads = Array.tabulate(2) { _ =>
      new Thread {
        override def run() {
          val r = new SimpleRandom
          for (i <- 0 until 100000) {
            if (r.nextInt(2) == 0) {
              if (m(0) != "okay") {
                failed() = i
                return
              }
            } else {
              atomic { implicit txn =>
                m(0) = "should be isolated"
                m.snapshot
                m(0) = "okay"
              }
            }
          }
        }
      }
    }
    for (t <- threads) t.start()
    for (t <- threads) t.join()
    assert(failed() === -1)
  }

  //////// perf stuff

  private def now = System.currentTimeMillis

  test("sequential non-txn read performance", Slow) {
    for (pass <- 0 until 4) {
      for (size <- List(10, 100, 1000, 100000)) {
        val m = TMap(kvRange(0, size): _*).single
        val t0 = now
        var i = 0
        var k = 0
        while (i < 1000000) {
          assert(m.contains(k) == (k < size))
          i += 1
          k = if (k == 2 * size - 1) 0 else k + 1
        }
        val elapsed = now - t0
        println("TMap: non-txn read: " + size + " keys/map -> " + elapsed + " nanos/contain")
      }
    }
  }

  test("sequential non-txn append performance", Slow) {
    for (pass <- 0 until 2) {
      for (size <- List(10, 100, 1000, 100000)) {
        val src = kvRange(0, size).toArray
        val t0 = now
        var outer = 0
        while (outer < 1000000) {
          TMap.empty[Int, String].single ++= src
          outer += size
        }
        val elapsed = now - t0
        println("TMap: non-txn append: " + size + " keys/map -> " + elapsed + " nanos/added-key")
      }
    }
  }

  test("sequential non-txn update performance", Slow) {
    val values = (0 until 37) map { "x" + _ }
    for (pass <- 0 until 2) {
      for (size <- List(10, 100, 1000, 100000)) {
        val m = TMap(kvRange(0, size): _*).single
        val t0 = now
        var i = 0
        while (i < 1000000) {
          val prev = m.put(i % size, values(i % values.length))
          assert(!prev.isEmpty)
          i += 1
        }
        val elapsed = now - t0
        println("TMap: non-txn update: " + size + " keys/map -> " + elapsed + " nanos/put")
      }
    }
  }

  test("sequential non-txn put/remove mix performance", Slow) {
    val values = (0 until 37) map { "x" + _ }
    val rand = new skel.SimpleRandom
    for (pass <- 0 until 4) {
      for (size <- List(10, 100, 1000, 100000)) {
        val m = TMap(kvRange(0, size): _*).single
        val t0 = now
        var i = 0
        while (i < 1000000) {
          val r = rand.nextInt()
          val k = math.abs(r % size)
          if (r > 0)
            m.put(k, values(i % values.length))
          else
            m.remove(k)
          i += 1
        }
        val elapsed = now - t0
        println("TMap: non-txn put/remove: " + size + " keys/map -> " + elapsed + " nanos/op")
      }
    }
  }

  test("sequential txn read performance", Slow) {
    for (txnSize <- List(2, 10, 1000)) {
      for (pass <- 0 until 2) {
        for (size <- List(10, 100, 1000, 100000)) {
          val m = TMap(kvRange(0, size): _*).single
          val t0 = now
          for (ii <- 0 until 1000000 by txnSize) {
            atomic { implicit txn =>
              var i = ii
              while (i < ii + txnSize) {
                val k = i % (2 * size)
                assert(m.contains(k) == (k < size))
                i += 1
              }
            }
          }
          val elapsed = now - t0
          println("TMap: txn read: " + txnSize + " accesses/txn: " + size + " keys/map -> " + elapsed + " nanos/op")
        }
      }
    }
  }

  test("sequential txn put/remove mix performance", Slow) {
    val values = (0 until 37) map { "x" + _ }
    val rand = new skel.SimpleRandom
    for (txnSize <- List(2, 10, 1000)) {
      for (pass <- 0 until 2) {
        for (size <- List(10, 100, 1000, 100000)) {
          val m = TMap(kvRange(0, size): _*).single
          val t0 = now
          for (ii <- 0 until 1000000 by txnSize) {
            atomic { implicit txn =>
              var i = ii
              while (i < ii + txnSize) {
                val r = rand.nextInt()
                val k = math.abs(r % size)
                if (r > 0)
                  m.put(k, values(i % values.length))
                else
                  m.remove(k)
                i += 1
              }
            }
          }
          val elapsed = now - t0
          println("TMap: txn put/remove: " + txnSize + " accesses/txn: " + size + " keys/map -> " + elapsed + " nanos/op")
        }
      }
    }
  }

  test("TxnDebuggable") {
    val m1 = TMap[Int, Int]()
    val m2 = TMap(1 -> "one")
    val m3 = TMap(1 -> "one", 2 -> "two").single
    val m4 = TMap(kvRange(0, 10000): _*).single

    assert(m1.dbgStr === "TMap[size=0]()")
    assert(m2.dbgStr === "TMap[size=1](1 -> one)")
    assert(m3.dbgStr == "TMap[size=2](1 -> one, 2 -> two)" ||
           m3.dbgStr == "TMap[size=2](2 -> two, 1 -> one)")
    assert(m4.dbgStr.startsWith("TMap[size=10000]("))
    assert(m4.dbgStr.length >= 1000)
    assert(m4.dbgStr.length < 1100)

    assert(m1.dbgValue.asInstanceOf[Array[_]].length === 0)
    assert(m2.dbgValue.asInstanceOf[Array[_]].length === 1)
    assert(m3.dbgValue.asInstanceOf[Array[_]].length === 2)
    assert(m4.dbgValue.asInstanceOf[Array[_]].length === 10000)
  }
}
