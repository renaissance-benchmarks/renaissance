package tutorial



import io.reactors._
import org.scalatest._
import scala.concurrent.Promise
import scala.concurrent.ExecutionContext
import org.scalatest.funsuite.AsyncFunSuite



class GuideJvmHelloWorld extends AsyncFunSuite {
  val system = new ReactorSystem("test-system")

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("start on a dedicated thread") {
    val done = Promise[String]()
    def println(s: String) = done.success(s)

    import io.reactors._

    object HelloWorld {
      def main(args: Array[String]) {
        val welcomeReactor = Reactor[String] {
          self =>
            self.main.events onEvent { name =>
              println(s"Welcome, $name!")
              self.main.seal()
            }
        }
        val system = ReactorSystem.default("test-system")
        /*!begin-include!*/
        /*!begin-code!*/
        val ch = system.spawn(
          welcomeReactor.withScheduler(JvmScheduler.Key.newThread))
        /*!end-code!*/
        /*!end-include(reactors-scala-jvm-spawn-thread.html)!*/
        ch ! "Alan"
      }
    }

    HelloWorld.main(Array())

    done.future.map(s => assert(s == "Welcome, Alan!"))
  }
}
