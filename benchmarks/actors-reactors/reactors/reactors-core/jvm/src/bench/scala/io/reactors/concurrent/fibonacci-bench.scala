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



class FibonacciBench extends JBench.OfflineReport {
  override def defaultConfig = Context(
    exec.minWarmupRuns -> 20,
    exec.maxWarmupRuns -> 40,
    exec.benchRuns -> 48,
    exec.independentSamples -> 4,
    verbose -> true
  )

  override def reporter = Reporter.Composite(
    new RegressionReporter(tester, historian),
    new MongoDbReporter[Double],
    new HtmlReporter(true)
  )

  val sizes = Gen.range("size")(25, 25, 5)

  @transient lazy val system = new ReactorSystem("reactor-bench")

  @gen("sizes")
  @benchmark("io.reactors.fibonacci")
  @curve("onEvent")
  def reactorOnEvent(sz: Int) = {
    val done = Promise[Int]()

    def fib(parent: Channel[Int], n: Int): Unit = {
      system.spawn(Reactor[Int] { self =>
        if (n < 2) {
          parent ! 1
          self.main.seal()
        } else {
          var sum = 0
          var recv = 0
          self.main.events.onEvent { x =>
            sum += x
            recv += 1
            if (recv == 2) {
              parent ! sum
              self.main.seal()
            }
          }
          fib(self.main.channel, n - 1)
          fib(self.main.channel, n - 2)
        }
      })
    }

    system.spawn(Reactor[Int] { self =>
      self.main.events.onEvent { x =>
        done.success(x)
      }
      fib(self.main.channel, sz)
    })

    Await.ready(done.future, 10.seconds)
  }

  var actorSystem: ActorSystem = _

  def akkaSetup() {
    actorSystem = ActorSystem("actor-bench")
  }

  def akkaTeardown() {
    actorSystem.terminate()
  }

  @gen("sizes")
  @benchmark("io.reactors.fibonacci")
  @curve("akka")
  @setupBeforeAll("akkaSetup")
  @teardownAfterAll("akkaTeardown")
  def akka(sz: Int) = {
    val done = Promise[Int]()

    actorSystem.actorOf(
      Props.create(classOf[FibonacciRootActor], done, new Integer(sz)))

    Await.ready(done.future, 10.seconds)
  }
}


class FibonacciRootActor(done: Promise[Int], n: Int) extends Actor {
  override def preStart() {
    context.actorOf(Props.create(classOf[FibonacciActor], self, new Integer(n)))
  }
  def receive = {
    case x: Integer => done.success(x)
  }
}


class FibonacciActor(parent: ActorRef, n: Int) extends Actor {
  var sum = 0
  var recv = 0
  override def preStart() {
    if (n < 2) {
      parent ! 1
      context.stop(self)
    } else {
      context.actorOf(Props.create(classOf[FibonacciActor], self, new Integer(n - 1)))
      context.actorOf(Props.create(classOf[FibonacciActor], self, new Integer(n - 2)))
    }
  }
  def receive = {
    case n: Integer =>
      sum += n
      recv += 1
      if (recv == 2) {
        parent ! sum
        context.stop(self)
      }
  }
}
