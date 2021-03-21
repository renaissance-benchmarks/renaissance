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



class ForkJoinThroughputBench extends JBench.OfflineReport {
  override def defaultConfig = Context(
    exec.minWarmupRuns -> 30,
    exec.maxWarmupRuns -> 60,
    exec.benchRuns -> 72,
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
  @benchmark("io.reactors.fork-join-throughput")
  @curve("onEvent")
  def reactorOnEvent(sz: Int) = {
    val done = new Array[Promise[Boolean]](ForkJoinThroughputBench.K)
    for (i <- 0 until ForkJoinThroughputBench.K) done(i) = Promise[Boolean]()

    val workers = (for (i <- 0 until ForkJoinThroughputBench.K) yield {
      system.spawn(Reactor[String] { self =>
        var count = 0
        self.main.events.on {
          count += 1
          if (count == sz) {
            done(i).success(true)
            self.main.seal()
          }
        }
      })
    }).toArray

    val producer = system.spawn(Reactor[String] { self =>
      var j = 0
      while (j < sz) {
        var i = 0
        while (i < ForkJoinThroughputBench.K) {
          workers(i) ! "event"
          i += 1
        }
        j += 1
      }
    })

    for (i <- 0 until ForkJoinThroughputBench.K) {
      Await.result(done(i).future, 10.seconds)
    }
  }

  var actorSystem: ActorSystem = _

  def akkaSetup() {
    actorSystem = ActorSystem("actor-bench")
  }

  def akkaTeardown() {
    actorSystem.terminate()
  }

  @gen("sizes")
  @benchmark("io.reactors.fork-join-throughput")
  @curve("akka")
  @setupBeforeAll("akkaSetup")
  @teardownAfterAll("akkaTeardown")
  def akka(sz: Int) = {
    val done = new Array[Promise[Boolean]](ForkJoinThroughputBench.K)
    for (i <- 0 until ForkJoinThroughputBench.K) done(i) = Promise[Boolean]()

    val workers = (for (i <- 0 until ForkJoinThroughputBench.K) yield {
      actorSystem.actorOf(
        Props.create(classOf[ForkJoinThroughputActor], new Integer(sz), done(i)))
    }).toArray

    var j = 0
    while (j < sz) {
      var i = 0
      while (i < ForkJoinThroughputBench.K) {
        workers(i) ! "event"
        i += 1
      }
      j += 1
    }

    for (i <- 0 until ForkJoinThroughputBench.K) {
      Await.result(done(i).future, 10.seconds)
    }
  }
}


object ForkJoinThroughputBench {
  val K = 128
}


class ForkJoinThroughputActor(sz: Int, done: Promise[Boolean]) extends Actor {
  var count = 0
  def receive = {
    case s: String =>
      count += 1
      if (count == sz) {
        done.success(true)
        context.stop(self)
      }
  }
}
