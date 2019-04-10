/* scala-stm - (c) 2009-2016, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite
import skel.SimpleRandom
import java.util.concurrent.TimeUnit
import concurrent.forkjoin.LinkedTransferQueue
import util.control.Breaks

class CommitBarrierSuite extends FunSuite {

  test("single member commit") {
    val x = Ref(0)
    val cb = CommitBarrier(Long.MaxValue)
    val m = cb.addMember()
    val z = m.atomic { implicit t =>
      x() = x() + 1
      "result"
    }
    assert(z === Right("result"))
    assert(x.single() === 1)
  }

  test("single member cancel") {
    val x = Ref(0)
    val cb = CommitBarrier(60000)
    val m = cb.addMember()
    val z = m.atomic { implicit t =>
      m.cancel(CommitBarrier.UserCancel("cancel"))
      x() = x() + 1
      "result"
    }
    assert(z === Left(CommitBarrier.UserCancel("cancel")))
    assert(x.single() === 0)

    // commit barrier can still be used
    val m2 = cb.addMember()
    val z2 = m2.atomic { implicit t =>
      x() = x() + 1
      "result2"
    }
    assert(z2 === Right("result2"))
    assert(x.single() === 1)
  }

  test("single member failure") {
    val x = Ref(0)
    val cb = CommitBarrier(60000)
    val m = cb.addMember()
    intercept[Exception] {
      m.atomic { implicit t =>
        x() = x() + 1
        throw new Exception
      }
    }
    assert(x.single() === 0)

    // commit barrier is now dead
    intercept[IllegalStateException] {
      cb.addMember()
    }
  }

  test("override executor") {
    val x = Ref(0)
    val cb = CommitBarrier(60000)
    val m = cb.addMember()
    m.executor = m.executor.withRetryTimeout(10)
    intercept[InterruptedException] {
      m.atomic { implicit txn =>
        if (x() == 0)
          retry
        x() = 10
      }
    }
    assert(x.single() === 0)

    // commit barrier is now dead
    intercept[IllegalStateException] {
      cb.addMember()
    }
  }

  def parRun(n: Int)(body: Int => Unit) {
    // the CountDownLatch is not strictly necessary, but increases the chance
    // of truly concurrent execution
    val startingGate = new java.util.concurrent.CountDownLatch(1)

    val failure = Ref(null : Throwable)

    val threads = new Array[Thread](n)
    for (i <- 0 until n) {
      threads(i) = new Thread() {
        override def run() {
          startingGate.await()
          try {
            body(i)
          } catch {
            case x : Throwable => failure.single() = x
          }
        }
      }
      threads(i).start()
    }

    startingGate.countDown()

    for (t <- threads) {
      while (t.isAlive && failure.single() == null) {
        t.join(10)
      }
    }

    if (failure.single() != null) {
      throw failure.single()
    }
  }

  def runStress(barrierSize: Int,
                barrierCount: Int,
                check: Boolean = true,
                failurePct: Int = 0): Long = {
    val refs = Array.tabulate(barrierSize) { _ => Ref(0) }
    val cbs = Array.tabulate(barrierCount) { _ => CommitBarrier(60000) }
    val members = Array.tabulate(barrierCount, barrierSize) { (i, _) => cbs(i).addMember() }
    val t0 = System.nanoTime
    parRun(barrierSize + (if (check) 1 else 0)) { j =>
      val rand = new SimpleRandom()
      if (j == barrierSize) {
        // we are the cpu-hogging observer
        var prev = 0
        var samples = 0
        while (prev < barrierCount) {
          val x = refs(rand.nextInt(barrierSize)).single()
          assert(x >= prev)
          prev = x
          samples += 1
          if ((samples % 137) == 0) {
            // give single-threaded machines a fighting chance
            Thread.`yield`()
          }
        }
      } else {
        // we are a member
        for (m <- members) {
          // failurePct/2 out of 100% -> cancel before atomic
          // failurePct/2 out of 100% -> cancel inside atomic
          val p = rand.nextInt(200)
          if (p < failurePct)
            m(j).cancel(CommitBarrier.UserCancel("early"))

          m(j).atomic { implicit txn =>
            assert(p >= failurePct)
            if (p < failurePct * 2)
              m(j).cancel(CommitBarrier.UserCancel("late, inside"))
            refs(j) += 1
          }
        }
      }
    }
    System.nanoTime - t0
  }

  test("stress 2") {
    runStress(2, 10000)
  }

  test("stress 10") {
    runStress(10, 500)
  }

  test("stress 400") {
    runStress(400, 10)
  }

  test("partial success 2") {
    runStress(2, 10000, false, 25)
  }

  test("partial success 400") {
    runStress(400, 10, false, 75)
  }

  test("perf 2") {
    val count = 20000
    val elapsed = runStress(2, count, false)
    println("commit barrier, 2 threads, " + (elapsed / count) + " nanos/barrier")
  }

  test("perf 10") {
    val count = 2000
    val elapsed = runStress(10, count, false)
    println("commit barrier, 10 threads, " + (elapsed / count) + " nanos/barrier")
  }

  test("timeout") {
    val refs = Array.tabulate(2) { _ => Ref(0) }
    val cb = CommitBarrier(100, TimeUnit.MILLISECONDS)
    val members = Array.tabulate(2) { _ => cb.addMember() }
    val t0 = System.currentTimeMillis
    val elapsed = Array(0L, 0L)
    parRun(2) { i =>
      try {
        val z = members(i).atomic { implicit txn =>
          refs(i)() = 1
          if (i == 1) Thread.sleep(200)
        }
        assert(z === Left(CommitBarrier.Timeout))
        assert(refs(i).single() === 0)
      } finally {
        elapsed(i) = System.currentTimeMillis - t0
      }
    }
    assert(elapsed(0) >= 100 && elapsed(0) < 150, elapsed.toList)
    assert(elapsed(1) >= 200, elapsed.toList)
  }

  test("interrupt") {
    val refs = Array.tabulate(2) { _ => Ref(0) }
    val cb = CommitBarrier(60000)
    val members = Array.tabulate(2) { _ => cb.addMember() }
    val target = new LinkedTransferQueue[Thread]()
    parRun(3) { i =>
      if (i == 0) {
        // thread 0 is slow
        val z = members(i).atomic { implicit txn =>
          refs(i)() = 1
          Thread.sleep(100)
          "result"
        }
        assert(z.isLeft)
        assert(z.left.get.isInstanceOf[CommitBarrier.MemberUncaughtExceptionCause])
        assert(z.left.get.asInstanceOf[CommitBarrier.MemberUncaughtExceptionCause].x.isInstanceOf[InterruptedException])
        assert(refs(i).single() === 0)
      } else if (i == 1) {
        // thread 1 must wait and receives the interrupt
        intercept[InterruptedException] {
          members(i).atomic { implicit txn =>
            refs(i)() = 1
            target.put(Thread.currentThread())
          }
        }
      } else {
        target.take().interrupt()
      }
    }
  }

  test("control flow exception") {
    val slower = Ref(0)
    val ref = Ref(0)
    val cb = CommitBarrier(60000)
    val b = new Breaks()

    b.breakable {
      while (true) {
        val m = cb.addMember()
        new Thread() {
          override def run() {
            Thread.sleep(100)
            m.atomic { implicit txn =>
              slower() = slower() + 1
            }
          }
        }.start()
        cb.addMember().atomic { implicit txn =>
          ref() = ref() + 1
          b.break
        }
      }
    }

    assert(slower.single() === 1)
    assert(ref.single() === 1)
  }

  def doCycle(cycleSize: Int) {
    val refs = Array.tabulate(cycleSize) { _ => Ref(0) }
    val cb = CommitBarrier(60000)
    val members = Array.tabulate(cycleSize) { _ => cb.addMember() }
    parRun(cycleSize) { i =>
      val z = members(i).atomic { implicit txn =>
        refs(i) += 1
        refs((i + 1) % cycleSize) += 1
      }
      assert(z.isLeft)
      assert(z.left.get.isInstanceOf[CommitBarrier.MemberCycle])
    }
  }

  test("cycle 2 x 1000") {
    for (i <- 0 until 1000)
      doCycle(2)
  }

  test("cycle 3 x 1000") {
    for (i <- 0 until 1000)
      doCycle(3)
  }

  test("cycle 1000 x 3") {
    for (i <- 0 until 3)
      doCycle(1000)
  }

  test("auto-cancel") {
    for (reps <- 0 until 1000) {
      val cb = CommitBarrier(60000)
      var i = 0
      val commits = new java.util.concurrent.atomic.AtomicInteger(0)
      val x = Ref(0)
      val y = Ref(0)
      val z = cb.addMember().atomic { implicit txn =>
        x() = 1
        val m = cb.addMember()
        i += 1
        val t = new Thread() {
          override def run() {
            m.atomic { implicit txn =>
              y() = i
              txn.afterCommit { _ => commits.incrementAndGet() }
            }
          }
        }
        t.start()
        txn.afterCommit { _ => t.join() }
        if (i < 10)
          Txn.rollback(Txn.OptimisticFailureCause('test, None))
        "hello"
      }
      assert(z === Right("hello"))
      assert(commits.get() === 1)
      assert(x.single() === 1)
      assert(y.single() === 10)
    }
  }

  test("no auto-cancel") {
    val x = Ref(0)
    val cb = CommitBarrier(60000)
    var t: Thread = null
    val outer = cb.addMember()
    outer.atomic { implicit txn =>
      val inner = cb.addMember(false)
      t = new Thread() {
        override def run() {
          inner.atomic { implicit txn =>
            x() = x() + 1
          }
        }
      }
      t.start()

      outer.cancel(CommitBarrier.UserCancel("cancel outer"))
    }
    t.join()
    assert(x.single() === 1)
  }

  test("embedded orAtomic") {
    val x = Ref(0)
    val y = Ref(0)
    val z = CommitBarrier(60000).addMember().atomic { implicit txn =>
      atomic { implicit txn =>
        y() = 1
        if (x() == 0)
          retry
        "first"
      } orAtomic { implicit txn =>
        x() = 1
        if (y() == 1)
          retry
        "second"
      }
    }
    assert(z === Right("second"))
    assert(x.single() === 1)
    assert(y.single() === 0)
  }

  test("recursive") {
    val commits = Ref(0).single
    def body(m: CommitBarrier.Member, depth: Int)(implicit txn: InTxn) {
      if (depth < 8) {
        for (m <- Array.tabulate(2) { _ => m.commitBarrier.addMember() }) {
          new Thread() {
            override def run() {
              m.atomic { implicit txn =>
                body(m, depth + 1)
                Txn.afterCommit { _ => commits += 1 }
              }
            }
          }.start()
        }
      }
    }
    val m = CommitBarrier(60000).addMember()
    m.atomic { implicit txn => body(m, 0) }

    // by sleeping and then awaiting we can (probabilistically) catch both
    // too few and too many commits
    Thread.sleep(100)
    commits.await { _ == 510 }
  }

  test("multi-barrier deadlock cycle") {
    for (tries <- 0 to 100) {
      val a1 = Ref(0)
      val a2 = Ref(0)

      val cb1 = CommitBarrier(1000)
      val cb1m1 = cb1.addMember()
      val cb1m2 = cb1.addMember()
      val cb2 = CommitBarrier(1000)
      val cb2m1 = cb2.addMember()
      val cb2m2 = cb2.addMember()

      val t1 = new Thread() {
        override def run() {
          cb1m1.atomic { implicit txn => a1() = a1() + 1 } 
        }
      }
      val t2 = new Thread() {
        override def run() {
          cb1m2.atomic { implicit txn => a2() = a2() + 1 }
        }
      }
      val t3 = new Thread() {
        override def run() {
          cb2m1.atomic { implicit txn => a1() = a1() + 1 }
        }
      }
      val t4 = new Thread() {
        override def run() {
          cb2m2.atomic { implicit txn => a2() = a2() + 1 }
        }
      }

      t1.start(); t2.start(); t3.start(); t4.start()
      t1.join(); t2.join(); t3.join(); t4.join()

      assert(a1.single() == 2);
      assert(a2.single() == 2);
    }
  }
}
