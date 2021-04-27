package tutorial



import io.reactors._
import org.scalatest._
import scala.concurrent._



class JsReactors extends AsyncFunSuite {
  implicit override def executionContext = ExecutionContext.Implicits.global

  test("use JS scheduler") {
    val system = ReactorSystem.default("test")
    val done = Promise[Boolean]()
    val proto = Reactor[Unit] { self =>
      self.sysEvents onMatch {
        case ReactorStarted =>
          done.success(true)
          self.main.seal()
      }
    }
    /*!begin-include!*/
    /*!begin-code!*/
    system.spawn(proto.withScheduler(JsScheduler.Key.default))
    /*!end-code!*/
    /*!end-include(reactors-scala-js-custom-scheduler.html)!*/
    done.future.map(t => assert(t))
  }
}
