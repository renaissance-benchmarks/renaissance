/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite
import java.util.concurrent.{ CountDownLatch, TimeUnit }

/** Contains extended tests of `retry`, `retryFor` and `tryAwait`.  Some basic
 *  tests are included in `TxnSuite`.
 */
class RetrySuite extends FunSuite {

  def timingAssert(ok: Boolean) {
    if (!ok) {
      val x = new Exception("timing-sensitive check failed, continuing")
      x.printStackTrace()
    }
  }

  test("retry set accumulation across alternatives") {
    val x = Ref(false)
    val b = new CountDownLatch(1)

    // this prevents the test from deadlocking
    new Thread("trigger") {
      override def run {
        b.await()
        Thread.sleep(10)
        x.single() = true
      }
    } start

    atomic { implicit t =>
      // The following txn and its alternative decode the value of x that was
      // observed, without x being a part of the current read set.
      val f = atomic { implicit t =>
        atomic { implicit t =>
          // this txn encodes the read of x in its retry state
          if (!x()) retry
        }
        true
      } orAtomic { implicit t =>
        false
      }
      if (!f) {
        // we've correctly observed x() == false, now arrange for true
        b.countDown()
        retry
      }
    }
  }

  test("tryAwait is conservative") {
    val x = Ref(10)
    val t0 = System.currentTimeMillis
    assert(!x.single.tryAwait(100)( _ == 0 ))
    val elapsed = System.currentTimeMillis - t0
    assert(elapsed >= 100)
    println("tryAwait(.., 100) took " + elapsed + " millis")
  }

  test("tryAwait in atomic is conservative") {
    val x = Ref(10)
    val t0 = System.currentTimeMillis
    val f = atomic { implicit txn => x.single.tryAwait(100)( _ == 0 ) }
    assert(!f)
    val elapsed = System.currentTimeMillis - t0
    assert(elapsed >= 100)
    println("tryAwait(.., 100) inside atomic took " + elapsed + " millis")
  }

  test("retryFor is conservative") {
    val x = Ref(false)
    val t0 = System.currentTimeMillis
    val s = atomic { implicit txn =>
      if (!x()) retryFor(100)
      "timeout"
    }
    assert(s === "timeout")
    val elapsed = System.currentTimeMillis - t0
    assert(elapsed >= 100)
    println("retryFor(100) took " + elapsed + " millis")
  }

  test("retryFor earliest is first") {
    val x = Ref(false)
    val s = atomic { implicit txn =>
      if (!x()) retryFor(100)
      "first"
    } orAtomic { implicit txn =>
      if (!x()) retryFor(200)
      "second"
    }
    assert(s === "first")
  }

  test("retryFor earliest is second") {
    val x = Ref(false)
    val s = atomic { implicit txn =>
      if (!x()) retryFor(300)
      "first"
    } orAtomic { implicit txn =>
      if (!x()) retryFor(100)
      "second"
    }
    assert(s === "second")
  }

  test("retryFor earliest is first nested") {
    val x = Ref(false)
    val s = atomic { implicit txn =>
      atomic { implicit txn =>
        if (!x()) retryFor(100)
        "first"
      } orAtomic { implicit txn =>
        if (!x()) retryFor(200)
        "second"
      }
    }
    assert(s === "first")
  }

  test("retryFor earliest is second nested") {
    val x = Ref(false)
    val s = atomic { implicit txn =>
      atomic { implicit txn =>
        if (!x()) retryFor(300)
        "first"
      } orAtomic { implicit txn =>
        if (!x()) retryFor(100)
        "second"
      }
    }
    assert(s === "second")
  }

  test("retryFor only is first") {
    val x = Ref(false)
    val s = atomic { implicit txn =>
      if (!x()) retryFor(100)
      "first"
    } orAtomic { implicit txn =>
      if (!x()) retry
      "second"
    }
    assert(s === "first")
  }

  test("retryFor only is second") {
    val x = Ref(false)
    val s = atomic { implicit txn =>
      if (!x()) retry
      "first"
    } orAtomic { implicit txn =>
      if (!x()) retryFor(100)
      "second"
    }
    assert(s === "second")
  }

  test("retryFor ladder") {
    val buf = new StringBuilder
    val x = Ref(0)
    atomic { implicit txn =>
      buf += 'a'
      retryFor(1)
      buf += 'b'
      retryFor(1)
      buf += 'c'
      retryFor(0)
      buf += 'd'
      retryFor(1)
      buf += 'e'
      retryFor(1)
      buf += 'f'
    } orAtomic { implicit txn =>
      if (x() == 0) retry
    }
    assert(buf.toString === "aababcdabcdeabcdef")
  }

  test("late start retryFor") {
    val x = Ref(0)
    val b = new CountDownLatch(1)
    val begin = System.currentTimeMillis
    var lastRetryForElapsed = 0L

    (new Thread { override def run {
      b.await()
      x.single() = 1
    } }).start

    val buf = new StringBuilder
    atomic { implicit txn =>
      buf += 'a'
      b.countDown()
      if (x() == 0) retry
      buf += 'b'
      val t = System.currentTimeMillis
      retryFor(200)
      lastRetryForElapsed = System.currentTimeMillis - t
      buf += 'c'
    }
    val elapsed = System.currentTimeMillis - begin
    println("late start retryFor(200) inside atomic took " + elapsed + " millis")
    assert(elapsed >= 200)
    assert(lastRetryForElapsed < 100) // should be ~0
    assert(buf.toString === "aababc")
  }

  test("expired start retryFor") {
    val x = Ref(0)
    val begin = System.currentTimeMillis
    var totalRetryForElapsed = 0L

    (new Thread { override def run {
      Thread.sleep(200) ;
      x.single() = 1
    } }).start

    val buf = new StringBuilder
    atomic { implicit txn =>
      buf += 'a'
      if (x() == 0) retry
      buf += 'b'
      val t = System.currentTimeMillis
      retryFor(100)
      totalRetryForElapsed += System.currentTimeMillis - t
      buf += 'c'
    }
    val elapsed = System.currentTimeMillis - begin
    println("expired(200) start retryFor(100) inside atomic took " + elapsed + " millis")
    assert(elapsed >= 200)
    assert(totalRetryForElapsed < 100) // should be ~0
    assert(buf.toString === "aabc")
  }

  test("retryFor as sleep") {
    val begin = System.currentTimeMillis
    atomic { implicit txn => retryFor(100) }
    val elapsed = System.currentTimeMillis - begin
    println("retryFor(100) as sleep took " + elapsed + " millis")
    assert(elapsed >= 100)
  }

  ///////////// CURSOR

  test("second retryFor has shorter timeout") {
    val x = Ref(0)
    val b1 = new CountDownLatch(1)
    val b2 = new CountDownLatch(1)

    (new Thread {
      override def run {
        b1.await()
        Thread.sleep(10)
        x.single() = 1
        b2.await()
        Thread.sleep(100)
        x.single += 1
      }
    }).start
    atomic { implicit txn =>
      x() = x() + 10
      if (x() == 10) {
        b1.countDown()
        retryFor(200)
      } else if (x() == 11) {
        b2.countDown()
        retryFor(50)
      }
    }
    assert(x.single() === 11)
    x.single.await( _ == 12 )
  }

  test("retryFor via View await") {
    val x = Ref(0)
    (new Thread {
      override def run {
        Thread.sleep(50)
        x.single() = 1
        Thread.sleep(100)
        x.single += 1
      }
    }).start
    atomic { implicit txn =>
      x() = x() + 10
      x.single.await( _ == 11 )
      assert(!x.single.tryAwait(50)( _ == 12 ))
    }
    assert(x.single() === 11)
    x.single.await( _ == 12 )
  }

  test("skipped retryFor deadline is retained") {
    val begin = System.currentTimeMillis
    atomic { implicit txn =>
      val f = atomic { implicit txn =>
        retryFor(50)
        false
      } orAtomic { implicit txn =>
        true
      }
      if (f)
        retryFor(1000)
    }
    val elapsed = System.currentTimeMillis - begin
    assert(elapsed < 500)
  }

  test("concatenated failing tryAwait") {
    val begin = System.currentTimeMillis
    val x = Ref(0)
    atomic { implicit txn =>
      x.single.tryAwait(50)( _ != 0 )
      x.single.tryAwait(50)( _ != 0 )
      x.single.tryAwait(50)( _ != 0 )
    }
    val elapsed = System.currentTimeMillis - begin
    assert(elapsed > 150)
    timingAssert(elapsed < 200)
  }

  test("barging retry") {
    // the code to trigger barging is CCSTM-specific, but this test should pass regardless
    var tries = 0
    val x = Ref(0)
    val y = Ref(0)
    val z = Ref(0)
    val b = new CountDownLatch(1)

    (new Thread { override def run {
      b.await()
      Thread.sleep(10)
      x.single() = 1
      y.single() = 1
    } }).start

    atomic { implicit txn =>
      z() = 2
      atomic { implicit txn =>
        NestingLevel.current
        tries += 1
        if (tries < 50)
          Txn.rollback(Txn.OptimisticFailureCause('test, None))
        b.countDown()

        z() = 3
        x()
        if (y.swap(2) != 1)
          retry
      }
    }
  }

  test("retry with many pessimistic reads") {
    // the code to trigger barging is CCSTM-specific, but this test should pass regardless
    val b = new CountDownLatch(1)
    var tries = 0
    val refs = Array.tabulate(10000) { _ => Ref(0) }

    (new Thread { override def run {
      b.await()
      Thread.sleep(10)
      refs(500).single() = 1
    } }).start

    atomic { implicit txn =>
      tries += 1
      if (tries < 50)
        Txn.rollback(Txn.OptimisticFailureCause('test, None))

      val sum = refs.foldLeft(0)( _ + _.get )
      b.countDown()
      if (sum == 0)
        retry
    }
  }

  test("retry with many accesses to TArray") {
    // the code to trigger barging is CCSTM-specific, but this test should pass regardless
    val b = new CountDownLatch(1)
    var tries = 0
    val refs = TArray.ofDim[Int](10000).refs

    (new Thread { override def run {
      b.await()
      Thread.sleep(10)
      refs(500).single() = 1
    } }).start

    atomic { implicit txn =>
      tries += 1
      if (tries < 50)
        Txn.rollback(Txn.OptimisticFailureCause('test, None))

      for (r <- refs.take(500))
        r *= 2
      val sum = refs.foldLeft(0)( _ + _.get )
      b.countDown()
      if (sum == 0)
        retry
    }
  }

  test("futile retry should fail") {
    val x = true
    intercept[IllegalStateException] {
      atomic { implicit txn =>
        if (x)
          retry
      }
    }
  }

  test("withRetryTimeout") {
    val x = Ref(0)
    val t0 = System.currentTimeMillis
    intercept[InterruptedException] {
      atomic.withRetryTimeout(100000, TimeUnit.MICROSECONDS) { implicit txn =>
        if (x() == 0)
          retry
      }
    }
    val elapsed = System.currentTimeMillis - t0
    assert(elapsed >= 100)
    timingAssert(elapsed < 150)
  }

  test("retryFor wins over withRetryTimeout") {
    val x = Ref(0)
    val t0 = System.currentTimeMillis
    val f = atomic.withRetryTimeout(100) { implicit txn =>
      if (x() == 0) {
        retryFor(100)
        true
      } else
        false
    }
    assert(f)
    val elapsed = System.currentTimeMillis - t0
    assert(elapsed >= 100)
    timingAssert(elapsed < 150)
  }

  test("withRetryTimeout applies to retryFor") {
    val x = Ref(0)
    val t0 = System.currentTimeMillis
    intercept[InterruptedException] {
      atomic.withRetryTimeout(100) { implicit txn =>
        if (x() == 0)
          retryFor(101)
        assert(false)
      }
    }
    val elapsed = System.currentTimeMillis - t0
    assert(elapsed >= 100)
    timingAssert(elapsed < 150)
  }

  test("nested global withRetryTimeout") {
    val orig = TxnExecutor.defaultAtomic
    try {
      TxnExecutor.transformDefault( _.withRetryTimeout(100) )
      val x = Ref(0)
      val t0 = System.currentTimeMillis
      intercept[InterruptedException] {
        atomic { implicit txn =>
          atomic { implicit txn =>
            atomic { implicit txn =>
              if (x() == 0)
                retry
              assert(false)
            }
          }
        }
      }
      val elapsed = System.currentTimeMillis - t0
      println(elapsed)
      assert(elapsed >= 100)
      timingAssert(elapsed < 150)
    } finally {
      TxnExecutor.transformDefault( _ => orig )
    }
  }

  test("tighter timeout wins") {
    val t0 = System.currentTimeMillis
    intercept[InterruptedException] {
      atomic.withRetryTimeout(100) { implicit txn =>
        atomic.withRetryTimeout(1000) { implicit txn =>
          retry
        }
      }
    }
    val elapsed = System.currentTimeMillis - t0
    assert(elapsed >= 100)
    timingAssert(elapsed < 150)
  }

  test("non-timeout elapsed") {
    val x = Ref(0)
    (new Thread { override def run {
      Thread.sleep(100)
      x.single() = 1
    } }).start
    intercept[InterruptedException] {
      atomic { implicit txn =>
        atomic.withRetryTimeout(200) { implicit txn =>
          if (x() == 0)
            retry
        }
        atomic.withRetryTimeout(50) { implicit txn =>
          retryFor(51)
        }
      }
    }
  }
}
