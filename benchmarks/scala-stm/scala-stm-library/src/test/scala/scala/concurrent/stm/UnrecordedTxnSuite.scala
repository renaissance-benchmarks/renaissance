/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import org.scalatest.FunSuite
import java.util.concurrent.CountDownLatch


class UnrecordedTxnSuite extends FunSuite {

  test("fixed unrecorded txn") {
    val z = atomic.unrecorded { implicit txn => "foo" }
    assert(z === "foo")
  }

  test("nested fixed unrecorded txn") {
    val x = Ref(0)
    val z = atomic { implicit txn =>
      x() = 1
      atomic.unrecorded { implicit txn => "foo" }
    }
    assert(z === "foo")
  }

  test("writing unrecorded txn") {
    val x = Ref(0)
    val z = atomic.unrecorded { implicit txn =>
      x() = 1
      "foo"
    }
    assert(z === "foo")
    assert(x.single() === 0)
  }

  test("nested unrecorded txn") {
    val x = Ref(0)
    val z = atomic.unrecorded { implicit txn =>
      x += 1
      atomic.unrecorded { implicit txn =>
        x += 1
        atomic.unrecorded { implicit txn =>
          x += 1
          atomic.unrecorded { implicit txn =>
            x += 1
            atomic.unrecorded { implicit txn =>
              x += 1
              atomic.unrecorded { implicit txn =>
                x += 1
                atomic.unrecorded { implicit txn =>
                  x()
                }
              }
            }
          }
        }
      }
    }
    assert(z === 6)
    assert(x.single() === 0)
  }

  test("nested new write unrecorded txn") {
    val x = Ref(0)
    val z = atomic { implicit txn =>
      atomic.unrecorded { implicit txn =>
        x() = 1
        "foo"
      }
    }
    assert(x.single() === 0)
    assert(z === "foo")
  }

  test("nested update unrecorded txn") {
    val x = Ref(0)
    val z = atomic { implicit txn =>
      x() = 1
      atomic.unrecorded { implicit txn =>
        x() = 2
        "foo"
      }
    }
    assert(x.single() === 1)
    assert(z === "foo")
  }

  test("nested preceding unrecorded txn") {
    val x = Ref(0)
    val z = atomic { implicit txn =>
      val z = atomic.unrecorded { implicit txn =>
        x() = 2
        "foo"
      }
      x() = 1
      z
    }
    assert(x.single() === 1)
    assert(z === "foo")
  }

  test("read set emptied") {
    val b = new CountDownLatch(1)
    val e = new CountDownLatch(1)

    val x = Ref(0)

    new Thread {
      override def run() {
        b.await()
        x.single() = 1
        e.countDown()
      }
    }.start()

    var tries = 0
    val (z1, z2) = atomic { implicit txn =>
      tries += 1
      val z1 = atomic.unrecorded { implicit txn => x() }
      b.countDown()
      e.await()
      (z1, x())
    }

    assert(z1 === 0)
    assert(z2 === 1)
    assert(tries === 1)
  }

  class TestException extends Exception

  test("outerFailure handler") {

    val x = Ref(0)

    var z: Any = null
    intercept[TestException] {
      atomic { implicit txn =>
        val level = NestingLevel.root
        val done = new CountDownLatch(1)
        new Thread {
          override def run() {
            level.requestRollback(Txn.UncaughtExceptionCause(new TestException))
            done.countDown()
          }
        }.start()
        done.await()

        z = atomic.unrecorded({ implicit txn => x() }, { cause => cause })
      }
    }

    assert(z.isInstanceOf[Txn.UncaughtExceptionCause])
  }
}