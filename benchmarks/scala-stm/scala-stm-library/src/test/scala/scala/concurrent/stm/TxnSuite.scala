/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite
import java.util.concurrent.CountDownLatch


class TxnSuite extends FunSuite {

  test("empty transaction") {
    atomic { implicit t =>
      () // do nothing
    }
  }

  test("atomic function") {
    val answer = atomic { implicit t =>
      42
    }
    assert(Integer.parseInt(answer.toString, 13) === 6*9)
  }

  test("large transaction") {
    val refs = Array.tabulate(10000) { i => Ref(i) }
    atomic { implicit txn =>
      for (r <- refs)
        r() = r() + 1
    }
  }

  test("duplicate view with old access") {
    val x = Ref(1)
    atomic { implicit t =>
      val b1 = x.single
      assert(b1.get === 1)
      val b2 = x.single
      assert(b2.get === 1)
      b1() = 2
      assert(b1.get === 2)
      assert(b2.get === 2)
      b2() = 3
      assert(b1.get === 3)
      assert(b2.get === 3)
    }
    assert(x.single.get === 3)
  }

  class UserException extends Exception

  test("failure atomicity") {
    val x = Ref(1)
    intercept[UserException] {
      atomic { implicit t =>
        x() = 2
        throw new UserException
      }
    }
    assert(x.single.get === 1)
  }

  test("non-local return") {
    val x = Ref(1)
    val y = nonLocalReturnHelper(x)
    assert(x.single.get === 2)
    assert(y === 2)
  }

  def nonLocalReturnHelper(x: Ref[Int]): Int = {
    atomic { implicit t =>
      x() = x() + 1
      return x()
    }
    -1
  }

  test("strings") {
    atomic.toString
    atomic.withRetryTimeout(100).toString
    atomic { implicit txn => txn.toString }
    atomic { implicit txn => NestingLevel.root.toString }
  }

  test("basic retry") {
    val x = Ref(0)
    val y = Ref(false)
    val b = new CountDownLatch(1)
    new Thread {
      override def run() {
        b.await()
        Thread.sleep(10)
        y.single() = true
        x.single() = 1
      }
    }.start()

    atomic { implicit txn =>
      b.countDown()
      if (x() == 0)
        retry
    }
    assert(y.single())
  }

  test("nested retry") {
    val x = Ref(0)
    val y = Ref(false)
    val b = new CountDownLatch(1)
    new Thread {
      override def run() {
        b.await()
        Thread.sleep(10)
        y.single() = true
        x.single() = 1
      }
    }.start()

    atomic { implicit txn =>
      atomic { implicit txn =>
        // this will cause the nesting to materialize
        NestingLevel.current

        b.countDown()
        if (x() == 0)
          retry
      }
    }
    assert(y.single())
  }

  test("simple orAtomic") {
    val x = Ref(0)
    val f = atomic { implicit txn =>
      if (x() == 0)
        retry
      false
    } orAtomic { implicit txn =>
      true
    }
    assert(f)    
  }

  test("single atomic.oneOf") {
    val x = Ref("zero")
    atomic.oneOf({ implicit txn =>
      x() = "one"
    })
    assert(x.single() === "one")
  }

  test("atomic.oneOf") {
    val refs = Array(Ref(false), Ref(false), Ref(false))
    for (w <- 0 until 3) {
      new Thread("wakeup") {
        override def run() {
          Thread.sleep(200)
          refs(w).single() = true
        }
      }.start()
      oneOfExpect(refs, w, Array(0))
    }
  }

  test("nested atomic.oneOf") {
    val refs = Array(Ref(false), Ref(false), Ref(false))
    for (w <- 0 until 3) {
      new Thread("wakeup") {
        override def run() {
          Thread.sleep(200)
          refs(w).single() = true
        }
      }.start()
      val retries = Array(0)
      atomic { implicit txn => oneOfExpect(refs, w, retries) }
    }
  }

  test("alternative atomic.oneOf") {
    val a = Ref(0)
    val refs = Array(Ref(false), Ref(false), Ref(false))
    for (w <- 0 until 3) {
      new Thread("wakeup") {
        override def run() {
          Thread.sleep(200)
          refs(w).single() = true
        }
      }.start()
      val retries = Array(0)
      val f = atomic { implicit txn =>
        if (a() == 0)
          retry
        false
      } orAtomic { implicit txn =>
        oneOfExpect(refs, w, retries)
        true
      }
      assert(f)
    }
  }

  private def oneOfExpect(refs: Array[Ref[Boolean]], which: Int, sleeps: Array[Int]) {
    val result = Ref(-1)
    atomic.oneOf(
        { t: InTxn => implicit val txn = t; result() = 0 ; if (!refs(0)()) retry },
        { t: InTxn => implicit val txn = t; if (refs(1)()) result() = 1 else retry },
        { t: InTxn => implicit val txn = t; if (refs(2)()) result() = 2 else retry },
        { t: InTxn => implicit val txn = t; sleeps(0) += 1 ; retry }
      )
    refs(which).single() = false
    assert(result.single.get === which)
    if (sleeps(0) != 0)
      assert(sleeps(0) === 1)
  }

  test("orAtomic w/ exception") {
    intercept[UserException] {
      atomic { implicit t =>
        if ("likely".hashCode != 0)
          retry
      } orAtomic { implicit t =>
        throw new UserException
      }
    }
  }

  test("Atomic.orAtomic") {
    val x = Ref(1)
    def a() = {
      atomic { implicit t =>
        if (x() > 1) true else retry
      } orAtomic { implicit t =>
        false
      }
    }
    assert(a() === false)
    x.single() = 2
    assert(a() === true)
  }

  test("simple nesting") {
    val x = Ref(10)
    atomic { implicit t =>
      x += 1
      atomic { implicit t =>
        assert(x.get === 11)
        x += 2
      }
      assert(x.get === 13)
    }
    assert(x.single.get === 13)
  }

  test("partial rollback") {
    val x = Ref("none")
    atomic { implicit t =>
      x() = "outer"
      try {
        atomic { implicit t =>
          x() = "inner"
          throw new UserException
        }
      } catch {
        case _: UserException =>
      }
    }
    assert(x.single() === "outer")
  }

  test("partial rollback of transform") {
    val x = Ref("none")
    atomic { implicit t =>
      x() = "outer"
      try {
        atomic { implicit t =>
          x.transform { _ + "inner" }
          throw new UserException
        }
      } catch {
        case _: UserException =>
      }
    }
    assert(x.single() === "outer")
  }

  test("partial rollback due to invalid read") {
    val x = Ref(0)
    val y = Ref(0)

    (new Thread { override def run() { Thread.sleep(100) ; y.single() = 1 } }).start()

    atomic { implicit t =>
      x()
      atomic { implicit t =>
        y()
        Thread.sleep(200)
        y()
      } orAtomic { implicit t =>
        throw new Error("should not be run")
      }
    } orAtomic { implicit t =>
      throw new Error("should not be run")
    }
  }

  test("View in txn") {
    val x = Ref(10)
    val xs = x.single
    atomic { implicit t =>
      x += 1
      assert(x() === 11)
      assert(xs() === 11)
      xs += 1
      assert(x() === 12)
      assert(xs() === 12)
      x.single += 1
      assert(x() === 13)
      assert(xs() === 13)
      assert(x.single() === 13)
      x.single() = 14
      assert(x() === 14)
    }
  }

  test("currentLevel during nesting") {
    // this test is _tricky_, because an assertion failure inside the atomic
    // block might cause a restart that expands any subsumption
    val (n0, n1, n2) = atomic { implicit t =>
      val (n1, n2) = atomic { implicit t =>
        val n2 = atomic { implicit t =>
          NestingLevel.current
        }
        (NestingLevel.current, n2)
      }
      (NestingLevel.current, n1, n2)
    }
    assert(n2.parent.get eq n1)
    assert(n2.root eq n0)
    assert(n1.parent.get eq n0)
    assert(n1.root eq n0)
    assert(n0.parent.isEmpty)
  }

  test("persistent rollback") {
    val x = Ref(0)
    var okay = true
    intercept[UserException] {
      atomic { implicit txn =>
        x() = 1
        try {
          Txn.rollback(Txn.UncaughtExceptionCause(new UserException()))
        } catch {
          case _: Throwable => // swallow
        }
        x()
        okay = false
      }
    }
    assert(okay)
  }

  test("persistent rollback via exception") {
    val x = Ref(0)
    intercept[UserException] {
      atomic { implicit txn =>
        x() = 1
        try {
          Txn.rollback(Txn.UncaughtExceptionCause(new UserException()))
        } catch {
          case _: Throwable => // swallow
        }
        throw new InterruptedException // this should be swallowed
      }
    }
  }

  test("many multi-level reads") {
    val refs = Array.tabulate(10000) { _ => Ref(0) }
    atomic { implicit txn =>
      for (r <- refs) r() = 1
      val f = atomic { implicit txn =>
        for (r <- refs) r() = 2
        if (refs(0)() != 0)
          retry
        false
      } orAtomic { implicit txn =>
        true
      }
      assert(f)
    }
    for (r <- refs)
      assert(r.single() === 1)
  }

  test("partial rollback of invalid read") {
    val x = Ref(0)
    var xtries = 0
    val y = Ref(0)
    var ytries = 0

    (new Thread { override def run() { Thread.sleep(100) ; y.single() = 1 } }).start()

    atomic { implicit txn =>
      xtries += 1
      x += 1
      atomic { implicit txn =>
        ytries += 1
        y()
        Thread.sleep(200)
        y()
      } orAtomic { implicit txn =>
        throw new Error("should not be run")
      }
    }

    // We can't assert, because different STMs might do different things.
    // For CCSTM it should be 1, 2
    println("xtries = " + xtries + ", ytries = " + ytries)
  }

  test("await") {
    val x = Ref(0)

    new Thread {
      override def run() {
        Thread.sleep(50)
        x.single() = 1
        Thread.sleep(50)
        x.single() = 2
      }
    }.start()

    x.single.await( _ == 2 )
    assert(x.single() === 2)
  }

  test("remote cancel") {
    val x = Ref(0)

    val finished = atomic { implicit txn =>
      x += 1
      NestingLevel.current
    }
    assert(x.single() === 1)

    for (i <- 0 until 100) {
      intercept[UserException] {
        atomic { implicit txn =>
          val active = NestingLevel.current
          new Thread {
            override def run() {
              val cause = Txn.UncaughtExceptionCause(new UserException)
              assert(finished.requestRollback(cause) === Txn.Committed)
              assert(active.requestRollback(cause) == Txn.RolledBack(cause))
            }
          }.start()

          while (true)
            x() = x() + 1
        }
      }
      assert(x.single() === 1)
    }
  }

  test("remote cancel of root") {
    val x = Ref(0)

    val finished = atomic { implicit txn =>
      x += 1
      NestingLevel.current
    }
    assert(x.single() === 1)

    for (i <- 0 until 100) {
      intercept[UserException] {
        atomic { implicit txn =>
          // this is to force true nesting for CCSTM, but the test should pass for any STM
          atomic { implicit txn => NestingLevel.current }

          val active = NestingLevel.current
          new Thread {
            override def run() {
              Thread.`yield`()
              Thread.`yield`()
              val cause = Txn.UncaughtExceptionCause(new UserException)
              assert(finished.requestRollback(cause) === Txn.Committed)
              assert(active.requestRollback(cause) == Txn.RolledBack(cause))
            }
          }.start()

          while (true)
            atomic { implicit txn => x += 1 }
        }
      }
      assert(x.single() === 1)
    }
  }

  test("remote cancel of child") {
    val x = Ref(0)

    for (i <- 0 until 100) {
      intercept[UserException] {
        atomic { implicit txn =>
          atomic { implicit txn =>
            val active = NestingLevel.current
            new Thread {
              override def run() {
                Thread.`yield`()
                Thread.`yield`()
                val cause = Txn.UncaughtExceptionCause(new UserException)
                assert(active.requestRollback(cause) == Txn.RolledBack(cause))
              }
            }.start()

            while (true)
              x() = x() + 1
          }
        }
      }
      assert(x.single() === 0)
    }
  }

  test("toString") {
    (atomic { implicit txn =>
      txn.toString
      txn
    }).toString
    (atomic { implicit txn =>
      NestingLevel.current.toString
      NestingLevel.current
    }).toString
  }

  test("many simultaneous Txns", Slow) {
    // CCSTM supports 2046 simultaneous transactions
    val threads = Array.tabulate(2500) { _ => new Thread {
      override def run() { atomic { implicit txn => Thread.sleep(1000) } }
    }}
    val begin = System.currentTimeMillis
    for (t <- threads) t.start()
    for (t <- threads) t.join()
    val elapsed = System.currentTimeMillis - begin
    println(threads.length + " empty sleep(1000) txns took " + elapsed + " millis")
  }

  perfTest("uncontended R+W txn perf") { (x, y) =>
    var i = 0
    while (i < 5) {
      i += 1
      atomic { implicit t =>
        assert(x() == "abc")
        x() = "def"
      }
      atomic { implicit t =>
        assert(x() == "def")
        x() = "abc"
      }
    }
  }

  for (depth <- List(0, 1, 2, 8)) {
    perfTest("uncontended R+W txn perf: nesting depth " + depth) { (x, y) =>
      var i = 0
      while (i < 5) {
        i += 1
        nested(depth) { implicit t =>
          assert(x() == "abc")
          x() = "def"
        }
        nested(depth) { implicit t =>
          assert(x() == "def")
          x() = "abc"
        }
      }
    }
  }

  perfTest("uncontended R+R txn perf") { (x, y) =>
    var i = 0
    while (i < 10) {
      i += 1
      atomic { implicit t =>
        assert(x() == "abc")
        assert(y() == 10)
      }
    }
  }

  for (depth <- List(0, 1, 2, 8)) {
    perfTest("uncontended R+R txn perf: nesting depth " + depth) { (x, y) =>
      var i = 0
      while (i < 10) {
        i += 1
        nested(depth) { implicit t =>
          assert(x() == "abc")
          assert(y() == 10)
        }
      }
    }
  }

//  for (i <- 0 until 50) {
//    perfTest("uncontended R+R txn perf: nesting depth 8, take " + i) { (x, y) =>
//      var i = 0
//      while (i < 10) {
//        i += 1
//        nested(8) { implicit t =>
//          assert(x() == "abc")
//          assert(y() == 10)
//        }
//      }
//    }
//  }

  private def nested(depth: Int)(body: InTxn => Unit) {
    atomic { implicit txn =>
      if (depth == 0)
        body(txn)
      else
        nested(depth - 1)(body)
    }
  }

  private def perfTest(name: String)(runTen: (Ref[String], Ref[Int]) => Unit) {
    test(name, Slow) {
      val x = Ref("abc")
      val y = Ref(10)
      var best = java.lang.Long.MAX_VALUE
      for (pass <- 0 until 50000) {
        val begin = System.nanoTime
        runTen(x, y)
        val elapsed = System.nanoTime - begin
        best = best min elapsed
      }
      println(name + ": best was " + (best / 10.0) + " nanos/txn")
    }
  }
}
