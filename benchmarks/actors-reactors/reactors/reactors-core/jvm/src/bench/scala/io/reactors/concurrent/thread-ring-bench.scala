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



class ThreadRingBench extends JBench.OfflineReport {
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
  @benchmark("io.reactors.thread-ring")
  @curve("onEvent")
  def reactorOnEventThreadRing(sz: Int) = {
    val done = Promise[Boolean]()

    class Ring {
      val ringIds = (0 until ThreadRingBench.RING_SIZE).toArray
      val ring: Array[Channel[Int]] = for (i <- ringIds) yield {
        system.spawn(Reactor[Int] { self =>
          var rounds = sz / ThreadRingBench.RING_SIZE
          self.main.events.onEvent { x =>
            rounds -= 1
            if (rounds == 0) {
              self.main.seal()
              if (i == ring.length - 1) done.success(true)
            }
            ring((i + 1) % ring.length) ! x
          }
        })
      }
      ring(0) ! 7
    }
    new Ring

    assert(Await.result(done.future, 10.seconds))
  }

  var actorSystem: ActorSystem = _

  def akkaThreadRingSetup() {
    actorSystem = ActorSystem("actor-bench")
  }

  def akkaThreadRingTeardown() {
    actorSystem.terminate()
  }

  @gen("sizes")
  @benchmark("io.reactors.thread-ring")
  @curve("akka")
  @setupBeforeAll("akkaThreadRingSetup")
  @teardownAfterAll("akkaThreadRingTeardown")
  def akkaThreadRing(sz: Int) = {
    val done = Promise[Boolean]()
    val ring = new Array[ActorRef](ThreadRingBench.RING_SIZE)
    for (i <- 0 until ring.length) {
      ring(i) = actorSystem.actorOf(
        Props.create(classOf[RingActor], new Integer(sz), new Integer(i), ring, done)) 
    }
    ring(0) ! 7
    assert(Await.result(done.future, 10.seconds))
  }
}


object ThreadRingBench {
  val RING_SIZE = 1000
}


class RingActor(
  val sz: Int, val i: Int, val ring: Array[ActorRef], val done: Promise[Boolean]
) extends Actor {
  var rounds = sz / ThreadRingBench.RING_SIZE
  def receive = {
    case x: Int =>
      rounds -= 1
      if (rounds == 0) {
        context.stop(self)
        if (i == ring.length - 1) done.success(true)
      }
      if (rounds > 0 || i != ring.length - 1) ring((i + 1) % ring.length) ! x
  }
}
