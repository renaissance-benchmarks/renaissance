package io.reactors
package concurrent



import io.reactors.services.Net
import io.reactors.test._
import java.io.InputStream
import java.net.URL
import java.util.concurrent.atomic.AtomicLong
import org.apache.commons.io._
import org.scalacheck.Properties
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Gen.choose
import org.scalatest._
import org.scalatest.concurrent.TimeLimitedTests
import scala.collection._
import scala.concurrent._
import scala.concurrent.duration._
import scala.util.Failure
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers



class NetTest extends AnyFunSuite with Matchers with BeforeAndAfterAll {

  val system = ReactorSystem.default("TestSystem")

  test("resource string should be resolved") {
    val res = Promise[String]()
    val resolver = (url: URL) => IOUtils.toInputStream("ok", "UTF-8")
    system.spawn(Proto[ResourceStringReactor](res, resolver)
      .withScheduler(JvmScheduler.Key.piggyback))
    assert(res.future.value.get.get == "ok", s"got ${res.future.value}")
  }

  test("resource string should throw an exception") {
    val testError = new Exception
    val res = Promise[String]()
    val resolver: URL => InputStream = url => throw testError
    system.spawn(Proto[ResourceStringReactor](res, resolver)
      .withScheduler(JvmScheduler.Key.piggyback))
    assert(res.future.value.get == Failure(testError), s"got ${res.future.value}")
  }

  override def afterAll() {
    system.shutdown()
  }

}


class ResourceStringReactor(val res: Promise[String], val resolver: URL => InputStream)
extends Reactor[Unit] {
  val net = new Net(system, resolver)
  val response = net.resourceAsString("http://dummy.url/resource.txt")
  response.ignoreExceptions onEvent { s =>
    res success s
    main.seal()
  }
  response onExcept { case t =>
    res failure t
    main.seal()
  }
}


object ChannelsCheck extends Properties("ChannelsCheck") with ExtendedProperties {

  val repetitions = 3
  val nameCounter = new AtomicLong(0L)

  property("channel should be awaited") =
    forAllNoShrink(detChoose(0, 7)) { n =>
      stackTraced {
        for (i <- 0 until repetitions) {
          val system = ReactorSystem.default("check-system")
          try {
            val checkReactorName = "check-reactor-" + nameCounter.getAndIncrement()
            val done = Promise[Boolean]()
            system.spawn(Reactor[Unit] { self =>
              system.channels.await[String](checkReactorName + "#main").onEvent { ch =>
                ch ! "done"
                self.main.seal()
              }
            })
            Thread.sleep(n * n)
            system.spawn(Reactor[String] { self =>
              self.main.events onMatch {
                case "done" =>
                  done.success(true)
                  self.main.seal()
              }
            } withName (checkReactorName))
            assert(Await.result(done.future, 10.seconds))
          } finally {
            system.shutdown()
          }
        }
        true
      }
    }

}
