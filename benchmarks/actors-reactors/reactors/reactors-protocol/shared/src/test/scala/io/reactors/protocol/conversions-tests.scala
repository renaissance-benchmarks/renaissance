package io.reactors
package protocol



import io.reactors.test._
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.collection._
import scala.concurrent._
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import org.scalatest.funsuite.AsyncFunSuite



class ConversionsSpec
extends AsyncFunSuite with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("conversions")

  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("Traversable#toEvents") {
    val events = Seq(1, 2, 3, 4).toEvents
    val buffer = mutable.Buffer[Int]()
    events.onEvent(buffer += _)
    assert(buffer == Seq(1, 2, 3, 4))
  }

  test("Future#toIVar") {
    val future = Future { 7 }
    val done = Promise[Boolean]()
    system.spawn(Reactor[String] { self =>
      future.toIVar on {
        done.success(true)
        self.main.seal()
      }
    })
    done.future.map(t => assert(t))
  }
}
