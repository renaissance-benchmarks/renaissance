/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite
import java.util.concurrent.CountDownLatch


class CallbackSuite extends FunSuite {

  class UserException extends Exception

  test("many callbacks") {
    var n = 0
    val x = Ref(0)
    atomic { implicit t =>
      x() = 1
      for (i <- 0 until 10000)
        Txn.afterCommit { _ => n += 1 }
    }
    assert(n === 10000)
    assert(x.single() === 1)
  }

  test("beforeCommit upgrade on read-only commit") {
    val x = Ref(0)
    var ran = false
    atomic { implicit t =>
      assert(x() === 0)
      Txn.beforeCommit { _ =>
        assert(!ran)
        x() = 1
        ran = true
      }
    }
    assert(ran)
    assert(x.single() === 1)
  }

  test("retry in beforeCommit") {
    val n = 50
    val x = Ref(0)
    val b = Array.tabulate(n) { _ => new CountDownLatch(1) }
    val t = new Thread("trigger") {
      override def run() {
        for (i <- 0 until n) {
          b(i).await()
          Thread.sleep(5)
          x.single() += 1
        }
      }
    }
    var tries = 0
    t.start()
    val y = Ref(0)
    atomic { implicit t =>
      tries += 1
      y() = 1
      Txn.beforeCommit { implicit t =>
        if (x() < n) {
          for (i <- 0 until math.min(n, tries))
            b(i).countDown()
          retry
        }
      }
    }
    assert(tries >= n)
  }

  test("exception in beforeCommit") {
    val x = Ref[Option[String]](Some("abc"))
    intercept[NoSuchElementException] {
      atomic { implicit t =>
        x() = None
        Txn.beforeCommit { _ => println(x().get) }
      }
    }
  }

  test("surviving beforeCommit") {
    val x = Ref(1)
    val y = Ref(2)
    val z = Ref(3)
    var a = false
    var aa = false
    var ab = false
    var b = false
    var ba = false
    var bb = false
    var bc = false
    atomic { implicit t =>
      Txn.beforeCommit { _ => assert(!a) ; a = true }
      atomic { implicit t =>
        Txn.beforeCommit { _ => assert(!aa) ; aa = true }
        x += 1
        if (x() != 0)
          retry
      } orAtomic { implicit t =>
        Txn.beforeCommit { _ => assert(!ab) ; ab = true }
        y += 1
        if (y() != 0)
          retry
      }
      z += 8
    } orAtomic { implicit t =>
      Txn.beforeCommit { _ => assert(!b && !ba && !bb && !bc) ; b = true }
      atomic { implicit t =>
        Txn.beforeCommit { _ => assert(!ba) ; ba = true }
        z += 1
        if (x() != 0)
          retry
      } orAtomic { implicit t =>
        Txn.beforeCommit { _ => assert(!bb) ; bb = true }
        x += 1
        if (x() != 0)
          retry
      } orAtomic { implicit t =>
        Txn.beforeCommit { _ => assert(b) ; assert(!bc) ; bc = true }
        if (x() + y() + z() == 0)
          retry
      }
      z += 16
    }
    assert(!a)
    assert(!aa)
    assert(!ab)
    assert(b)
    assert(!ba)
    assert(!bb)
    assert(bc)
    assert(x.single() == 1)
    assert(y.single() == 2)
    assert(z.single() == 19)
  }

  test("afterRollback on commit") {
    atomic { implicit t =>
      Txn.afterRollback { _ => assert(false) }
    }
  }

  test("afterRollback on rollback") {
    val x = Ref(10)
    var ran = false
    atomic { implicit t =>
      Txn.afterRollback { _ =>
        assert(!ran)
        ran = true
      }
      if (x() == 10) {
        val adversary = new Thread {
          override def run() {
            x.single.transform(_ + 1)
          }
        }
        adversary.start()
        adversary.join()
        x()
        assert(false)
      }
    }
    assert(ran)
  }

  test("afterCommit runs a txn") {
    var ran = false
    val x = Ref(0)
    atomic { implicit t =>
      x() = 1
      Txn.afterCommit { _ =>
        atomic { implicit t =>
          assert(!ran)
          ran = true
          assert(x() === 1)
          x() = 2
        }
      }
    }
    assert(ran)
    assert(x.single() === 2)
  }

  test("afterCommit doesn't access txn") {
    var ran = false
    val x = Ref(0)
    atomic { implicit t =>
      x() = 1
      Txn.afterCommit { _ =>
        intercept[IllegalStateException] {
          assert(!ran)
          ran = true
          x() = 2
        }
      }
    }
    assert(ran)
    assert(x.single() === 1)
  }

  test("beforeCommit during beforeCommit") {
    val handler = new Function1[InTxn, Unit] {
      var count = 0

      def apply(txn: InTxn) {
        if (txn eq null) {
          // this is the after-atomic check
          assert(count === 1000)
        } else {
          count += 1
          if (count < 1000)
            Txn.beforeCommit(this)(txn)
        }
      }
    }
    val x = Ref(0)
    atomic { implicit t =>
      x += 1
      Txn.beforeCommit(handler)
    }
    handler(null)
  }

  test("beforeCommit termination") {
    val x = Ref(0)
    var a = false
    intercept[UserException] {
      atomic { implicit t =>
        assert(x() === 0)
        Txn.beforeCommit { _ =>
          assert(!a)
          a = true
          throw new UserException
        }
        x += 2
        Txn.beforeCommit { _ =>
          assert(false)
        }
      }
    }
    assert(a)
  }

  test("manual optimistic retry") {
    var tries = 0
    val x = Ref(0)
    atomic { implicit t =>
      assert(x() === 0)
      x += tries
      tries += 1
      if (tries < 100)
        Txn.rollback(Txn.OptimisticFailureCause('manual_failure, None))
    }
    assert(x.single() === 99)
    assert(tries === 100)
  }

  test("manual optimistic retry during beforeCommit") {
    var tries = 0
    val x = Ref(0)
    atomic { implicit t =>
      assert(x() === 0)
      x += tries
      tries += 1
      Txn.beforeCommit { implicit t =>
        if (tries < 100)
          Txn.rollback(Txn.OptimisticFailureCause('manual_failure, None))
      }
    }
    assert(x.single() === 99)
    assert(tries === 100)
  }

  test("whilePreparing") {
    var i = 0
    var observed = -1
    val x = Ref(0)
    atomic { implicit txn =>
      i += 1
      x() = i
      Txn.whilePreparing { _ =>
        observed = i
        if (i < 4) Txn.rollback(Txn.OptimisticFailureCause('test, None))
      }
    }
    assert(x.single() == 4)
    assert(observed == 4)
    assert(i == 4)
  }

  test("whilePreparing throws exception") {
    intercept[UserException] {
      atomic { implicit txn =>
        Txn.whilePreparing { _ => throw new UserException }
      }
    }
  }

  test("whileCommitting") {
    var count = 0
    val x = Ref(0)
    atomic { implicit txn =>
      x() = 1
      Txn.whileCommitting { _ => count += 1 }
    }
    assert(x.single() == 1)
    assert(count == 1)
  }

  test("whileCommitting without any accesses") {
    var count = 0
    atomic { implicit txn =>
      Txn.whileCommitting { _ => count += 1 }
    }
    assert(count == 1)
  }

  test("whileCommitting ordering", Slow) {
    val numThreads = 10
    val numPutsPerThread = 100000
    val startingGate = new java.util.concurrent.CountDownLatch(1)
    val active = Ref(numThreads)
    val failure = Ref(null : Throwable)

    val x = Ref(0)
    val notifier = new scala.concurrent.forkjoin.LinkedTransferQueue[Int]()
    val EOF = -1

    for (i <- 1 to numThreads) {
      (new Thread {
        override def run() {
          try {
            startingGate.await()
            for (i <- 1 to numPutsPerThread) {
              atomic { implicit txn =>
                x() = x() + 1
                val y = x()
                Txn.whileCommitting { _ =>
                  if ((i & 127) == 0) // try to perturb the timing
                    Thread.`yield`()
                  notifier.put(y)
                }
              }
            }
          } catch {
            case xx: Throwable => failure.single() = xx
          }
          if (active.single.transformAndGet( _ - 1 ) == 0)
            notifier.put(EOF)
        }
      }).start()
    }

    startingGate.countDown()
    for (expected <- 1 to numThreads * numPutsPerThread)
      assert(expected === notifier.take())
    assert(EOF === notifier.take())

    if (failure.single() != null)
      throw failure.single()
  }

  test("accepting external decider") {
    val x = Ref(0)
    atomic { implicit txn =>
      x() = 1
      Txn.setExternalDecider(new Txn.ExternalDecider {
        def shouldCommit(implicit txn: InTxnEnd): Boolean = {
          assert(txn.status == Txn.Prepared)
          true
        }
      })
    }
    assert(x.single() === 1)
  }

  test("valid duplicate external decider") {
    val x = Ref(0)
    atomic { implicit txn =>
      x() = 1
      val d = new Txn.ExternalDecider {
        def shouldCommit(implicit txn: InTxnEnd): Boolean = {
          assert(txn.status == Txn.Prepared)
          true
        }
      }
      assert(d == d)
      Txn.setExternalDecider(d)
      Txn.setExternalDecider(d)
    }
    assert(x.single() === 1)
  }

  test("invalid duplicate external decider") {
    val x = Ref(0)
    intercept[IllegalArgumentException] {
      atomic { implicit txn =>
        x() = 1
        val d1 = new Txn.ExternalDecider { def shouldCommit(implicit txn: InTxnEnd): Boolean = true }
        val d2 = new Txn.ExternalDecider { def shouldCommit(implicit txn: InTxnEnd): Boolean = true }
        assert(d1 != d2)
        Txn.setExternalDecider(d1)
        Txn.setExternalDecider(d2)
      }
    }
    assert(x.single() === 0)
  }

  test("transient reject external decider") {
    val x = Ref(0)
    var tries = 0
    atomic { implicit txn =>
      tries += 1
      x() = tries
      Txn.setExternalDecider(new Txn.ExternalDecider {
        def shouldCommit(implicit txn: InTxnEnd): Boolean = {
          assert(txn.status == Txn.Prepared)
          tries == 3
        }
      })
    }
    assert(tries === 3)
    assert(x.single() === 3)
  }

  test("nested external deciders") {
    val x = Ref(0)
    var which = 0
    atomic { implicit txn =>
      atomic { implicit txn =>
        Txn.setExternalDecider(new Txn.ExternalDecider {
          def shouldCommit(implicit txn: InTxnEnd): Boolean = { which = 1 ; true }
        })
        if (x.swap(1) == 0)
          retry
      } orAtomic { implicit txn =>
        Txn.setExternalDecider(new Txn.ExternalDecider {
          def shouldCommit(implicit txn: InTxnEnd): Boolean = { which = 2 ; true }
        })
        if (x.swap(2) == 0)
          retry
      } orAtomic { implicit txn =>
        Txn.setExternalDecider(new Txn.ExternalDecider {
          def shouldCommit(implicit txn: InTxnEnd): Boolean = { which = 3 ; true }
        })
        x.swap(3)
      }
    }
    assert(which === 3)
    assert(x.single() === 3)
  }

  test("external decider throws exception") {
    var tries = 0
    val x = Ref(0)
    intercept[UserException] {
      atomic { implicit txn =>
        tries += 1
        x() = 1
        Txn.setExternalDecider(new Txn.ExternalDecider {
          def shouldCommit(implicit txn: InTxnEnd): Boolean = throw new UserException
        })
      }
    }
    assert(tries === 1)
    assert(x.single() === 0)
  }

  test("rethrown exception from whileCommitting handler") {
    val x = Ref(0)
    intercept[UserException] {
      val customAtomic = atomic.withPostDecisionFailureHandler { (status, failure) => throw failure }
      customAtomic { implicit txn =>
        Txn.whileCommitting { _ => throw new UserException }
        x() = 1
      }
    }
    assert(x.single() === 1)
  }

  test("swallowed exception from whileCommitting handler") {
    var swallowed: Throwable = null
    val x = Ref(0)
    val customAtomic = atomic.withPostDecisionFailureHandler { (status, failure) =>
      assert(swallowed === null)
      assert(status == Txn.Committing)
      swallowed = failure
    }
    customAtomic { implicit txn =>
      Txn.whileCommitting { _ => throw new UserException }
      x() = 1
    }
    assert(x.single() === 1)
    assert(swallowed.isInstanceOf[UserException])
  }

  test("rethrown exception from afterCommit handler") {
    val x = Ref(0)
    intercept[UserException] {
      val customAtomic = atomic.withPostDecisionFailureHandler { (status, failure) => throw failure }
      customAtomic { implicit txn =>
        Txn.afterCommit { _ => throw new UserException }
        x() = 1
      }
    }
    assert(x.single() === 1)
  }

  test("swallowed exception from afterCommit handler") {
    var swallowed: Throwable = null
    val x = Ref(0)
    val customAtomic = atomic.withPostDecisionFailureHandler { (status, failure) =>
      assert(swallowed === null)
      assert(status == Txn.Committed)
      swallowed = failure
    }
    customAtomic { implicit txn =>
      Txn.afterCommit { _ => throw new UserException }
      x() = 1
    }
    assert(x.single() === 1)
    assert(swallowed.isInstanceOf[UserException])
  }

  test("rethrown exception from afterRollback handler") {
    val x = Ref(0)
    intercept[UserException] {
      val customAtomic = atomic.withPostDecisionFailureHandler { (status, failure) => throw failure }
      customAtomic { implicit txn =>
        Txn.afterRollback { _ => throw new UserException }
        x() = 1
        throw new InterruptedException
      }
    }
    assert(x.single() === 0)
  }

  test("swallowed exception from afterRollback handler") {
    var swallowed: Throwable = null
    val x = Ref(0)
    val customAtomic = atomic.withPostDecisionFailureHandler { (status, failure) =>
      assert(swallowed === null)
      assert(status.isInstanceOf[Txn.RolledBack])
      swallowed = failure
    }
    intercept[InterruptedException] {
      customAtomic { implicit txn =>
        Txn.afterRollback { _ => throw new UserException }
        x() = 1
        throw new InterruptedException
      }
    }
    assert(x.single() === 0)
    assert(swallowed.isInstanceOf[UserException])
  }

  test("rethrow afterRollback exception cancels retry") {
    val x = Ref(0)
    intercept[UserException] {
      val customAtomic = atomic.withPostDecisionFailureHandler { (status, failure) => throw failure }
      customAtomic { implicit txn =>
        Txn.afterRollback { _ => throw new UserException }
        if (x() == 0)
          retry
      }
    }
    assert(x.single() === 0)
  }

  test("UserException as control flow") {
    val x = Ref(0)
    intercept[UserException] {
      val customAtomic = atomic.withControlFlowRecognizer {
        case x: UserException => true
      }
      customAtomic { implicit txn =>
        x() = 1
        throw new UserException
      }
    }
    assert(x.single() === 1)
  }
}
