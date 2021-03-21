package io.reactors
package protocol



import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Gen.choose
import org.scalatest._
import scala.collection._
import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration._



class PatternsCheck extends Properties("Patterns") with ExtendedProperties {
  val system = ReactorSystem.default("check-system")

  val sizes = detChoose(0, 50)

  property("throttle") = forAllNoShrink(sizes) {
    num =>
    stackTraced {
      val buffer = mutable.Buffer[Int]()
      val seen = Promise[Seq[Int]]()
      val ch = system.spawn(Reactor[Int] { self =>
        if (num == 0) seen.success(buffer)
        self.main.events.throttle(_ => 1.millis) onEvent { i =>
          buffer += i
          if (i == num - 1) {
            seen.success(buffer)
            self.main.seal()
          }
        }
      })
      for (i <- 0 until num) ch ! i
      try {
        assert(Await.result(seen.future, 10.seconds) == (0 until num))
      } catch {
        case t: Throwable =>
          println(num, buffer)
          throw t
      }
      true
    }
  }
}
