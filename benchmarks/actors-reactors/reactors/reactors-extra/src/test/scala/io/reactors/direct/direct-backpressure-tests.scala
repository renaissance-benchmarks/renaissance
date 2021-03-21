package io.reactors
package direct



import io.reactors.protocol._
import org.scalatest._
import org.scalatest.concurrent.TimeLimitedTests
import scala.collection._
import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers



class DirectBackpressureTest extends AnyFunSuite with Matchers with BeforeAndAfterAll {
  val system = ReactorSystem.default("test-system")

  // test("start backpressure and send messages") {
  //   val done = Promise[Int]()
  //   val worker = system.backpressurePerClient(50) { (events: Events[Int]) =>
  //     var sum = 0
  //     events onEvent { x =>
  //       sum += x
  //       if (x == 199) {
  //         done.success(sum)
  //         Reactor.self.main.seal()
  //       }
  //     }
  //   }

  //   val source = Reactor.direct[Unit] {
  //     val link: Backpressure.Link[Int] = receive(worker.link)
  //     var i = 0
  //     while (i < 200) {
  //       link ! i
  //       i += 1
  //     }
  //     Reactor.self.main.seal()
  //   }
  //   system.spawn(source)

  //   assert(Await.result(done.future, 5.seconds) == 199 * 200 / 2)
  // }

  override def afterAll() {
    system.shutdown()
  }
}
