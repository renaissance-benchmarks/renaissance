package io.reactors
package protocol



import io.reactors.common.afterTime
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.concurrent._
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import org.scalatest.funsuite.AsyncFunSuite



class RendezvousProtocolsSpec
extends AsyncFunSuite with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("rendezvous-protocols")

  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("rendezvous with self") {
    val a = Promise[Int]()
    val b = Promise[String]()
    system.spawnLocal[Unit] { self =>
      val rendez = self.system.channels.daemon.rendezvous[String, Int]
      self.system.clock.timeout(500.millis) on {
        (rendez.left ? "ok").onEvent(n => a.success(n))
      }
      self.system.clock.timeout(1.second) on {
        (rendez.right ? 7).onEvent(s => b.success(s))
      }
    }
    val p = for (x <- a.future; y <- b.future) yield (x, y)
    p.map(t => assert(t == (7, "ok")))
  }
}
