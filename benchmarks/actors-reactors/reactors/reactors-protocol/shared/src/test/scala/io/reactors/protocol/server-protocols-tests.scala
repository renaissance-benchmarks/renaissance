package io.reactors
package protocol



import io.reactors.common.afterTime
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.concurrent._
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import org.scalatest.funsuite.AsyncFunSuite



class ServerProtocolsSpec
extends AsyncFunSuite with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("server-protocols")

  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("request a reply from the server") {
    val p = Promise[Int]()
    val proto = Reactor[String] { self =>
      val server = system.channels.named("length-server").server[String, Int]
      server.events onEvent {
        case (s, ch) => ch ! s.length
      }
      self.sysEvents onMatch {
        case ReactorStarted =>
          (server.channel ? "ok") onEvent { len =>
            p.success(len)
            self.main.seal()
            server.seal()
          }
      }
    }
    system.spawn(proto)
    p.future.map(n => assert(n == 2))
  }

  test("request a reply from a server reactor") {
    val p = Promise[Int]()
    val server = system.server[Int, Int]((s, x) => x + 17)
    system.spawn(Reactor[Int] { self =>
      (server ? 11) onEvent { y =>
        p.success(y)
      }
    })
    p.future.map(t => assert(t == 28))
  }

  test("request a reply from an asynchronous server reactor") {
    val p = Promise[Int]()
    val server = system.spawn(Reactor[Server.Req[String, Int]] { self =>
      self.main.asyncServe { x =>
        system.clock.timeout(1.second).map(_ => x.toInt)
      }
    })
    system.spawn(Reactor[Unit] { self =>
      (server ? "17") onEvent { p.success(_) }
    })
    p.future.map(t => assert(t == 17))
  }
}
