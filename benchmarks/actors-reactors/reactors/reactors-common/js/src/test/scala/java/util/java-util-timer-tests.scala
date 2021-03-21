package java.util



import scala.concurrent._
import scala.concurrent.duration._
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests



class TimerTest extends AsyncFunSuite with AsyncTimeLimitedTests {

  def timeLimit = 10 seconds

  implicit override def executionContext =
    scala.concurrent.ExecutionContext.Implicits.global

  test("be scheduled once") {
    val done = Promise[Boolean]()
    val timer = new Timer
    timer.schedule(new TimerTask {
      def run() {
        done.success(true)
      }
    }, 1000)
    done.future.map(t => assert(t))
  }

}