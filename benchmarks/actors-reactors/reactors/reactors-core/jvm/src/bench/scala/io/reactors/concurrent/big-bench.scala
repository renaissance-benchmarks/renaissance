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
import scala.util.Failure
import scala.util.Random
import scala.util.Success



class BigBench extends JBench.OfflineReport {
  override def defaultConfig = Context(
    exec.minWarmupRuns -> 20,
    exec.maxWarmupRuns -> 40,
    exec.benchRuns -> 72,
    exec.independentSamples -> 8,
    verbose -> true
  )

  override def reporter = Reporter.Composite(
    new RegressionReporter(tester, historian),
    new MongoDbReporter[Double],
    new HtmlReporter(true)
  )

  val sizes = Gen.range("size")(250, 250, 50)

  @transient lazy val system = new ReactorSystem("reactor-bench")

  @gen("sizes")
  @benchmark("io.reactors.big")
  @curve("onEvent")
  def reactorOnEvent(sz: Int) = {
    import BigBench._
    val done = Promise[Boolean]()
    val workers = new Array[Channel[Cmd]](BigBench.N)

    val sink = system.spawn(Reactor[String] { self =>
      var left = BigBench.N
      self.main.events.on {
        left -= 1
        if (left == 0) {
          for (i <- 0 until BigBench.N) workers(i) ! End()
          done.success(true)
          self.main.seal()
        }
      }
    })

    for (i <- 0 until BigBench.N) workers(i) = system.spawn(Reactor[Cmd] {
      self =>
      val random = new Random
      var left = sz
      val responses = system.channels.open[String]
      val ping = Ping(responses.channel)
      def doPing() {
        workers(random.nextInt(workers.length)) ! ping
      }
      responses.events.on {
        left -= 1
        if (left > 0) doPing()
        else sink ! "done"
      }
      self.main.events.onMatch {
        case Ping(ch) => ch ! "pong"
        case Start() => doPing()
        case End() =>
          self.main.seal()
          responses.seal()
      }
    })
    for (i <- 0 until BigBench.N) workers(i) ! Start()

    assert(Await.result(done.future, 10.seconds))
  }

  var actorSystem: ActorSystem = _

  def akkaSetup() {
    actorSystem = ActorSystem("actor-bench")
  }

  def akkaTeardown() {
    actorSystem.terminate()
  }

  @gen("sizes")
  @benchmark("io.reactors.big")
  @curve("akka")
  @setupBeforeAll("akkaSetup")
  @teardownAfterAll("akkaTeardown")
  def akka(sz: Int) = {
    import BigBench._
    val done = Promise[Boolean]()
    val workers = new Array[ActorRef](BigBench.N)

    val sink = actorSystem.actorOf(
      Props.create(classOf[BigBenchSinkActor], workers, done))
    for (i <- 0 until BigBench.N) {
      workers(i) = actorSystem.actorOf(
        Props.create(classOf[BigBenchActor], workers, sink, new Integer(sz)))
    }
    for (i <- 0 until BigBench.N) workers(i) ! Start()

    Await.ready(done.future, 10.seconds)
  }
}


object BigBench {
  val N = 1280
  
  trait Cmd
  
  case class Ping(ch: Channel[String]) extends Cmd
  
  case class ActorPing(ref: ActorRef) extends Cmd

  case class Start() extends Cmd
  
  case class End() extends Cmd
}


class BigBenchSinkActor(val workers: Array[ActorRef], val done: Promise[Boolean])
extends Actor {
  import BigBench._
  var left = workers.length
  def receive = {
    case s: String =>
      left -= 1
      if (left == 0) {
        for (i <- 0 until workers.length) workers(i) ! End()
        context.stop(self)
        done.success(true)
      }
  }
}


class BigBenchActor(val workers: Array[ActorRef], val sink: ActorRef, val sz: Int)
extends Actor {
  import BigBench._
  val random = new Random
  var left = sz
  val ping = ActorPing(self)
  def doPing() {
    workers(random.nextInt(workers.length)) ! ping
  }
  def receive = {
    case Start() =>
      doPing()
    case ActorPing(ref) =>
      ref ! "pong"
    case End() =>
      context.stop(self)
    case s: String =>
      left -= 1
      if (left > 0) doPing()
      else sink ! "done"
  }
}
