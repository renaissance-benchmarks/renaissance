package io.reactors
package protocol



import io.reactors.common.afterTime
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.concurrent._
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import org.scalatest.funsuite.AsyncFunSuite



class ScatterGatherProtocolsSpec
extends AsyncFunSuite with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("scatter-gather-protocols")

  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("request a reply from a scatter gatherer") {
    val p = Promise[Seq[Int]]()
    val workers: Seq[Server[String, Int]] = for (i <- 0 until 5) yield
      system.server[String, Int]((_, x) => x.toInt)
    val server = system.spawn(Reactor[ScatterGather.Req[String, Int]] { self =>
      self.main.scatterGather(Router.roundRobin(workers))
    })
    val request = (0 until 24).map(_.toString)
    system.spawn(Reactor[Unit] { self =>
      (server ? request).onEvent(p.success(_))
    })
    p.future.map(t => assert(t == (0 until 24)))
  }
}
