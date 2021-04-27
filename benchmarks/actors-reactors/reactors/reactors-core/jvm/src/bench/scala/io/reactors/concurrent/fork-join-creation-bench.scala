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



class ForkJoinCreationBench extends JBench.OfflineReport {
  override def defaultConfig = Context(
    exec.minWarmupRuns -> 80,
    exec.maxWarmupRuns -> 120,
    exec.benchRuns -> 72,
    exec.independentSamples -> 8,
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
  @benchmark("io.reactors.fork-join-creation")
  @curve("onEvent")
  def reactorOnEvent(sz: Int) = {
    val done = new Array[Promise[Boolean]](sz)
    for (i <- 0 until sz) done(i) = Promise[Boolean]()

    val workers = (for (i <- 0 until sz) yield {
      system.spawn(Reactor[String] { self =>
        self.main.events.on {
          done(i).success(true)
          self.main.seal()
        }
      })
    }).toArray

    var i = 0
    while (i < sz) {
      workers(i) ! "event"
      i += 1
    }

    for (i <- 0 until sz) {
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
  @benchmark("io.reactors.fork-join-creation")
  @curve("akka")
  @setupBeforeAll("akkaSetup")
  @teardownAfterAll("akkaTeardown")
  def akka(sz: Int) = {
    val done = new Array[Promise[Boolean]](sz)
    for (i <- 0 until sz) done(i) = Promise[Boolean]()

    val workers = (for (i <- 0 until sz) yield {
      actorSystem.actorOf(
        Props.create(classOf[ForkJoinCreationActor], done(i)))
    }).toArray

    var i = 0
    while (i < sz) {
      workers(i) ! "event"
      i += 1
    }

    for (i <- 0 until sz) {
      Await.result(done(i).future, 10.seconds)
    }
  }
}


class ForkJoinCreationActor(done: Promise[Boolean]) extends Actor {
  var count = 0
  def receive = {
    case s: String =>
      done.success(true)
      context.stop(self)
  }
}
