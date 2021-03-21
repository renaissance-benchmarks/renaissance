package io.reactors
package concurrent



import akka.actor._
import java.util.concurrent.ForkJoinPool
import java.util.concurrent.atomic._
import org.scalameter.api._
import org.scalameter.japi.JBench
import scala.collection._
import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.util.Success
import scala.util.Failure



class StreamingPingPongBench extends JBench.OfflineReport {
  override def defaultConfig = Context(
    exec.minWarmupRuns -> 150,
    exec.maxWarmupRuns -> 300,
    exec.benchRuns -> 120,
    exec.independentSamples -> 6,
    verbose -> true
  )

  override def reporter = Reporter.Composite(
    new RegressionReporter(tester, historian),
    new MongoDbReporter[Double],
    new HtmlReporter(true)
  )

  val sizes = Gen.range("size")(25000, 25000, 5000)

  @transient lazy val system = new ReactorSystem("reactor-bench")

  @gen("sizes")
  @benchmark("io.reactors.streaming-ping-pong")
  @curve("onEvent")
  def reactorOnEventPingPong(sz: Int) = {
    val done = Promise[Boolean]()

    class PingPong {
      val ping: Channel[String] = system.spawn(Reactor { (self: Reactor[String]) =>
        val pong = system.spawn(Reactor { (self: Reactor[String]) =>
          var left = sz
          self.main.events onEvent { x =>
            ping ! "pong"
            left -= 1
            if (left == 0) self.main.seal()
          }
        })
        var left = sz
        for (i <- 0 until StreamingPingPongBench.WINDOW_SIZE) pong ! "ping"
        self.main.events onEvent { x =>
          left -= 1
          if (left > 0) {
            pong ! "ping"
          } else {
            done.success(true)
            self.main.seal()
          }
        }
      })
    }
    new PingPong

    assert(Await.result(done.future, 10.seconds))
  }

  var actorSystem: ActorSystem = _

  def akkaPingPongSetup() {
    actorSystem = ActorSystem("actor-bench")
  }

  def akkaPingPongTeardown() {
    actorSystem.terminate()
  }

  @gen("sizes")
  @benchmark("io.reactors.streaming-ping-pong")
  @curve("akka")
  @setupBeforeAll("akkaPingPongSetup")
  @teardownAfterAll("akkaPingPongTeardown")
  def akkaPingPong(sz: Int) = {
    val done = Promise[Boolean]()
    val pong = actorSystem.actorOf(
      Props.create(classOf[StreamingPingPongBench.Pong], new Integer(sz)))
    val ping = actorSystem.actorOf(
      Props.create(classOf[StreamingPingPongBench.Ping], pong, new Integer(sz), done))

    assert(Await.result(done.future, 10.seconds))
  }
}


object StreamingPingPongBench {
  val WINDOW_SIZE = 128

  class Pong(val sz: Integer) extends Actor {
    var left = sz.intValue
    def receive = {
      case _ =>
        left -= 1
        sender ! "pong"
        if (left == 0) context.stop(self)
    }
  }

  class Ping(val pong: ActorRef, val sz: Integer, val done: Promise[Boolean])
  extends Actor {
    var left = sz.intValue
    for (i <- 0 until WINDOW_SIZE) pong ! "ping"
    def receive = {
      case _ =>
        left -= 1
        if (left > 0) {
          sender ! "ping"
        } else {
          done.success(true)
          context.stop(self)
        }
    }
  }
}
