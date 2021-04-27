package io.reactors
package protocol



import io.reactors.common.SetSeq
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.collection._
import scala.concurrent.ExecutionContext
import scala.concurrent.Promise
import scala.concurrent.duration._
import org.scalatest.funsuite.AsyncFunSuite



class RouterProtocolsSpec
extends AsyncFunSuite with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("router-protocols")

  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("default router with single channel") {
    val done = Promise[Boolean]()
    system.spawn(Reactor[Int] { self =>
      val rc = system.channels.daemon.router[Int]
        .route(Router.roundRobin(Seq(self.main.channel)))
      rc.channel ! 17
      self.main.events onEvent { x =>
        if (x == 17) {
          done.success(true)
          self.main.seal()
        } else {
          done.success(false)
        }
      }
    })
    done.future.map(t => assert(t))
  }

  test("round robin should work correctly when targets change") {
    val done = Promise[Seq[Int]]()
    system.spawn(Reactor[Int] { self =>
      val seen = mutable.Buffer[Int]()
      val c1 = system.channels.open[Int]
      val c2 = system.channels.open[Int]
      val routees = new SetSeq[Channel[Int]]
      routees += self.main.channel
      val rc = system.channels.daemon.router[Int].route(Router.roundRobin(routees))
      rc.channel ! 17
      self.main.events onEvent { x =>
        seen += x
        routees -= self.main.channel += c1.channel += c2.channel
        rc.channel ! 18
      }
      c1.events onEvent { x =>
        seen += x
        c1.seal()
        done.success(seen)
      }
      c2.events onEvent { x =>
        seen += x
        c2.seal()
        rc.channel ! 19
      }
    })
    done.future.map(xs => assert(xs == Seq(17, 18, 19)))
  }
}
