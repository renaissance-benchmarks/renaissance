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



class CountingActorBench extends JBench.OfflineReport {
  override def defaultConfig = Context(
    exec.minWarmupRuns -> 80,
    exec.maxWarmupRuns -> 120,
    exec.benchRuns -> 72,
    exec.independentSamples -> 4,
    verbose -> true
  )

  override def reporter = Reporter.Composite(
    new RegressionReporter(tester, historian),
    new MongoDbReporter[Double],
    new HtmlReporter(true)
  )

  val sizes = Gen.range("size")(250000, 250000, 50000)

  @transient lazy val system = new ReactorSystem("reactor-bench")

  @gen("sizes")
  @benchmark("io.reactors.counting-actor")
  @curve("onEvent")
  def reactorOnEvent(sz: Int) = {
    val done = Promise[Int]()

    trait Cmd
    case class Increment() extends Cmd
    case class Get() extends Cmd

    val counting = system.spawn(Reactor[Cmd] { self =>
      var count = 0
      self.main.events.onMatch {
        case Increment() =>
          count += 1
        case Get() =>
          done.success(count)
          self.main.seal()
      }
    })

    val producer = system.spawn(Reactor[Unit] { self =>
      val inc = new Increment
      var i = 0
      while (i < sz) {
        counting ! inc
        i += 1
      }
      counting ! Get()
      self.main.seal()
    })

    assert(Await.result(done.future, 10.seconds) == sz)
  }

  var actorSystem: ActorSystem = _

  def akkaCountingActorSetup() {
    actorSystem = ActorSystem("actor-bench")
  }

  def akkaCountingActorTeardown() {
    actorSystem.terminate()
  }

  @gen("sizes")
  @benchmark("io.reactors.counting-actor")
  @curve("akka")
  @setupBeforeAll("akkaCountingActorSetup")
  @teardownAfterAll("akkaCountingActorTeardown")
  def akka(sz: Int) = {
    val done = Promise[Int]()
    val counting = actorSystem.actorOf(
      Props.create(classOf[CountingActor], done))
    val producer = actorSystem.actorOf(
      Props.create(classOf[ProducerActor], counting, new Integer(sz)))
    assert(Await.result(done.future, 10.seconds) == sz)
  }
}


class CountingActor(val done: Promise[Int]) extends Actor {
  var count = 0
  def receive = {
    case s: String =>
      count += 1
    case Nil =>
      done.success(count)
      context.stop(self)
  }
}


class ProducerActor(val counting: ActorRef, val sz: Int) extends Actor {
  override def preStart() {
    var i = 0
    while (i < sz) {
      counting ! "inc"
      i += 1
    }
    counting ! Nil
    context.stop(self)
  }
  def receive = PartialFunction.empty
}
