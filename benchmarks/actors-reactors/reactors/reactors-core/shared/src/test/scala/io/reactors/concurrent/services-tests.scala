package io.reactors
package concurrent



import io.reactors.test._
import java.io.InputStream
import java.net.URL
import java.util.concurrent.atomic.AtomicLong
import java.util.Timer
import java.util.TimerTask
import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Gen.choose
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.collection._
import scala.concurrent._
import scala.concurrent.duration._
import scala.util.Failure
import org.scalatest.funsuite.AsyncFunSuite
import org.scalatest.matchers.should.Matchers



class ClockTest extends AsyncFunSuite
with Matchers with BeforeAndAfterAll {

  val system = ReactorSystem.default("TestSystem")

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("periodic timer should fire 3 times") {
    val done = Promise[Boolean]()
    system.spawn(Proto[PeriodReactor](done))
    done.future.map(assert(_))
  }

  test("timeout should fire exactly once") {
    val timeoutCount = Promise[Int]()
    system.spawn(Proto[TimeoutReactor](timeoutCount))
    timeoutCount.future.map { x =>
      assert(x == 1, s"Total timeouts: ${timeoutCount.future.value}")
    }
  }

  test("countdown should accumulate 55") {
    val total = Promise[Seq[Int]]()
    system.spawn(Proto[CountdownReactor](total))
    total.future.map { x =>
      assert(x == Seq(10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0),
        s"Countdown values = ${total.future.value}")
    }
  }

  override def afterAll() {
    system.shutdown()
  }

}


class PeriodReactor(val done: Promise[Boolean]) extends Reactor[Unit] {
  var countdown = 3
  val clock: Subscription = system.clock.periodic(50.millis) on {
    countdown -= 1
    if (countdown <= 0) {
      main.seal()
      clock.unsubscribe()
      done.trySuccess(true)
    }
  }
}


class TimeoutReactor(val timeoutCount: Promise[Int]) extends Reactor[Unit] {
  var timeouts = 0
  system.clock.timeout(50.millis) on {
    timeouts += 1
    system.clock.timeout(500.millis) on {
      main.seal()
      timeoutCount.trySuccess(timeouts)
    }
  }
}


class CountdownReactor(val total: Promise[Seq[Int]]) extends Reactor[Unit] {
  val elems = mutable.Buffer[Int]()
  system.clock.countdown(10, 50.millis).onEventOrDone {
    x => elems += x
  } {
    main.seal()
    total.trySuccess(elems)
  }
}


class CustomServiceTest extends AsyncFunSuite
with Matchers with BeforeAndAfterAll with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("TestSystem")

  implicit override def executionContext = ExecutionContext.Implicits.global

  def timeLimit = 10.seconds

  test("custom service should be retrieved") {
    val done = Promise[Boolean]()
    system.spawn(Proto[CustomServiceReactor](done))
    done.future.map { t =>
      assert(t, s"Status: ${done.future.value}")
    }
  }

  override def afterAll() {
    system.shutdown()
  }
}


class CustomService(val system: ReactorSystem) extends Protocol.Service {
  val cell = RCell(0)

  def shutdown() {}
}


class CustomServiceReactor(val done: Promise[Boolean]) extends Reactor[Unit] {
  system.service[CustomService].cell := 1
  sysEvents onMatch {
    case ReactorStarted =>
      if (system.service[CustomService].cell() == 1) done.success(true)
      else done.success(false)
      main.seal()
  }
}


class ChannelsTest extends AsyncFunSuite
with Matchers with BeforeAndAfterAll with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("TestSystem")

  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("existing channel should be awaited") {
    val done = Promise[Boolean]()
    system.spawn(Reactor[Unit] { self =>
      val completer = system.channels.named("completer").open[String]
      completer.events onMatch {
        case "done" =>
          done.success(true)
          completer.seal()
      }
      system.channels.await[String]("test-reactor#completer").onEvent { ch =>
        ch ! "done"
        self.main.seal()
      }
    } withName("test-reactor"))
    done.future.map(t => assert(t))
  }

  test("non-existing channel should be awaited") {
    val done = Promise[Boolean]()
    system.spawn(Reactor[Unit] { self =>
      system.channels.await[String]("test-reactor#main").onEvent { ch =>
        ch ! "done"
        self.main.seal()
      }
    })
    val timer = new Timer(true)
    timer.schedule(new TimerTask {
      def run() = {
        system.spawn(Reactor[String] { self =>
          self.main.events onMatch {
            case "done" =>
              done.success(true)
              self.main.seal()
          }
        } withName("test-reactor"))
      }
    }, 1000)
    done.future.map(t => assert(t))
  }

  override def afterAll() {
    system.shutdown()
  }
}
