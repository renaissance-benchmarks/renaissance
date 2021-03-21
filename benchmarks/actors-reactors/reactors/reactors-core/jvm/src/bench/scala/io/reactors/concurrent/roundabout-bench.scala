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



class RoundaboutBench extends JBench.OfflineReport {
  override def defaultConfig = Context(
    exec.minWarmupRuns -> 80,
    exec.maxWarmupRuns -> 160,
    exec.benchRuns -> 72,
    exec.independentSamples -> 8,
    verbose -> false
  )

  override def reporter = Reporter.Composite(
    new RegressionReporter(tester, historian),
    new MongoDbReporter[Double],
    new HtmlReporter(true)
  )

  val sizes = Gen.range("size")(1000, 1000, 50)

  @transient lazy val system = new ReactorSystem("reactor-bench")

  @gen("sizes")
  @benchmark("io.reactors.roundabout")
  @curve("onEvent")
  def reactorOnEvent(sz: Int) = {
    import RoundaboutBench._
    val done = Promise[Boolean]()

    val roundabout = system.spawn(Reactor[Channel[Array[Channel[Int]]]] { self =>
      val connectors = for (i <- (0 until sz).toArray) yield {
        system.channels.open[Int]
      }
      var count = 0
      for (c <- connectors) c.events.on {
        count += 1
        if (count == RoundaboutBench.N) {
          connectors.foreach(_.seal())
          done.success(true)
        }
      }
      self.main.events.onEvent { ch =>
        ch ! connectors.map(_.channel)
        self.main.seal()
      }
    })

    val producer = system.spawn(Reactor[Array[Channel[Int]]] { self =>
      roundabout ! self.main.channel
      self.main.events.onEvent { chs =>
        var i = 0
        while (i < RoundaboutBench.N) {
          chs(i % sz) ! i
          i += 1
        }
        self.main.seal()
      }
    })

    assert(Await.result(done.future, 10.seconds))
  }
}


object RoundaboutBench {
  val N = 500000
}
