package io.reactors
package protocol



import io.reactors.common.afterTime
import io.reactors.test._
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.collection._
import scala.concurrent.Future
import scala.concurrent.Promise
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import org.scalatest.funsuite.AsyncFunSuite



class PatternsSpec
extends AsyncFunSuite with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("server-protocols")

  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("throttle") {
    val a0 = Promise[Int]()
    val a1 = Promise[Int]()
    val a2 = Promise[Int]()
    val ch = system.spawn(Reactor[Int] { self =>
      var left = 3
      self.main.events.throttle(_ => 1000.millis) onEvent { x =>
        left -= 1
        if (left == 2) a2.success(x)
        if (left == 1) a1.success(x)
        if (left == 0) {
          a0.success(x)
          self.main.seal()
        }
      }
    })
    ch ! 7
    ch ! 11
    ch ! 17
    val done = Promise[Boolean]()
    afterTime(600.millis) {
      assert(a2.future.value.get.get == 7)
      assert(a1.future.value == None)
      assert(a0.future.value == None)
      afterTime(1000.millis) {
        assert(a1.future.value.get.get == 11)
        assert(a0.future.value == None)
        afterTime(1000.millis) {
          assert(a0.future.value.get.get == 17)
          done.success(true)
        }
      }
    }
    done.future.map(t => assert(t))
  }

  def retryTest(delays: Seq[Duration])(
    check: Seq[Duration] => Unit
  ): Future[Assertion] = {
    val done = Promise[Boolean]()
    val seen = Promise[Seq[Duration]]()
    val start = System.currentTimeMillis()
    val server = system.spawn(Reactor[(Unit, Channel[Unit])] { self =>
      val timestamps = mutable.Buffer[Duration]()
      self.main.events onMatch { case (_, ch) =>
        val current = System.currentTimeMillis()
        timestamps += (current - start).millis
        if (timestamps.length == delays.length) {
          seen.success(timestamps.toList)
          ch ! (())
          self.main.seal()
        }
      }
    })
    val ch = system.spawn(Reactor[Unit] { self =>
      var left = 3
      retry(delays)(server ? (())) onEvent { _ =>
        self.main.seal()
        done.success(true)
      }
    })
    for {
      t <- done.future
      timestamps <- seen.future
    } yield {
      assert(t)
      check(timestamps)
      assert(true)
    }
  }

  test("retry regular") {
    retryTest(Backoff.regular(3, 1000.millis)) { timestamps =>
      assert(timestamps(0) > 0.millis && timestamps(0) < 500.millis)
      assert(timestamps(1) > 950.millis && timestamps(1) < 1500.millis)
      assert(timestamps(2) > 1950.millis && timestamps(2) < 2500.millis)
    }
  }

  test("retry linear") {
    retryTest(Backoff.linear(3, 1000.millis)) { timestamps =>
      assert(timestamps(0) >= 0.millis && timestamps(0) < 500.millis)
      assert(timestamps(1) >= 950.millis && timestamps(1) < 1500.millis)
      assert(timestamps(2) >= 2950.millis && timestamps(2) < 3500.millis)
    }
  }

  test("retry exponential") {
    retryTest(Backoff.exp(4, 1000.millis)) { timestamps =>
      assert(timestamps(0) >= 0.millis && timestamps(0) < 500.millis)
      assert(timestamps(1) >= 950.millis && timestamps(1) < 1500.millis)
      assert(timestamps(2) >= 2950.millis && timestamps(2) < 3500.millis)
      assert(timestamps(3) >= 6950.millis && timestamps(3) < 7500.millis)
    }
  }

  test("retry random exponential") {
    retryTest(Backoff.exp(3, 1000.millis)) { timestamps =>
      assert(timestamps(0) >= 0.millis && timestamps(0) < 500.millis)
      if (timestamps(1) >= 950.millis && timestamps(1) < 1500.millis) {
        assert(timestamps(2) >= 2950.millis && timestamps(2) < 5500.millis)
      } else if (timestamps(1) >= 1950.millis && timestamps(1) < 2500.millis) {
        assert(timestamps(2) >= 3950.millis && timestamps(2) < 6500.millis)
      } else {
        assert(false, timestamps)
      }
    }
  }
}
