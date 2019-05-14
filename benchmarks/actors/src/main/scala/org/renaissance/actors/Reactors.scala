package org.renaissance.actors

import io.reactors._
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration._
import scala.util.Random

@Name("reactors")
@Group("actors")
@Summary(
  "Runs benchmarks inspired by the Savina microbenchmark workloads in a sequence on Reactors.IO."
)
@Licenses(Array(License.MIT))
@Repetitions(10)
class Reactors extends RenaissanceBenchmark {

  // Code based on https://github.com/reactors-io/reactors
  // The original uses BSD 3-clause license, the result is compatible with MIT license.

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var scalingFactor: Double = 1

  private var system: ReactorSystem = null

  override def setUpBeforeAll(c: Config): Unit = {
    // Instantiate the default reactor system used throughout the benchmark.
    system = ReactorSystem.default("bench-system")

    if (c.functionalTest) {
      scalingFactor = 0.1
    }
  }

  override def tearDownAfterAll(c: Config): Unit = {
    // Shut down the reactor system.
    system.shutdown()
  }

  def runIteration(c: Config): Unit = {

    // TODO Address workload scaling. One option is to tune dimensions so that each workload sends roughly equal number of messages.

    println("Baseline workload: Reactor scheduling events")
    new Baseline(system).run((1000000 * scalingFactor).intValue())
    println("BigBench workload: Many-to-many message ping pong")
    new BigBench(system).run((4000 * scalingFactor).intValue())
    println("CountingActor workload: Single reactor event processing")
    new CountingActor(system).run((8000000 * scalingFactor).intValue())
    println("Fibonacci workload: Dynamic reactor mix with varying lifetimes")
    new Fibonacci(system).run((28 * scalingFactor).intValue())
    println("ForkJoinCreation workload: Reactor creation performance")
    new ForkJoinCreation(system).run((250000 * scalingFactor).intValue())
    println("ForkJoinThroughput workload: Reactor processing performance")
    new ForkJoinThroughput(system).run((21000 * scalingFactor).intValue())
    println("PingPong workload: Reactor pair sequential ping pong performance")
    new PingPong(system).run((1500000 * scalingFactor).intValue())
    println("StreamingPingPong workload: Reactor pair overlapping ping pong performance")
    new StreamingPingPong(system).run((5000000 * scalingFactor).intValue())
    println("Roundabout workload: Many channels reactor performance")
    new Roundabout(system).run((750000 * scalingFactor).intValue())
    println("ThreadRing workload: Reactor ring forwarding performance")
    new ThreadRing(system).run((2500000 * scalingFactor).intValue())
  }
}

/** Baseline benchmark workload.
 *
 *  Exercise the basic reactor scheduler functionality.
 *  Wait for the system event stream to indicate that the reactor is no longer scheduled,
 *  and send a new message to the main event stream to schedule the reactor in response.
 *
 *  Messages exchanged: sz
 */
class Baseline(val system: ReactorSystem) {

  def run(sz: Int) = {
    val done = Promise[Boolean]()

    system.spawn(Reactor[String] { self =>
      var left = sz
      self.sysEvents onMatch {
        case ReactorPreempted =>
          self.main.channel ! "more"
      }
      self.main.events onEvent { x =>
        left -= 1
        if (left == 0) {
          done.success(true)
          self.main.seal()
        }
      }
    })

    assert(Await.result(done.future, Duration.Inf))
  }
}

/** BigBench benchmark workload.
 *
 *  Motivated by the Savina Big benchmark.
 *
 *  Creates a constant number of workers, each with two channels, one for requests, one for responses.
 *  Once started, each worker picks another at random, sends it a ping, and waits for a pong in response.
 *
 *  Messages exchanged: 2 * N * sz (ping, pong) + 2 * N (start, end)
 */
class BigBench(val system: ReactorSystem) {
  trait Cmd
  case class Ping(ch: Channel[String]) extends Cmd
  case class Start() extends Cmd
  case class End() extends Cmd

  def run(sz: Int) = {
    val done = Promise[Boolean]()
    val workers = new Array[Channel[Cmd]](BigBench.N)

    // Coordinator reactor. Responsible for reaping workers at the end of the workload.
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

    // Worker reactors. Responsible for pinging and ponging.
    for (i <- 0 until BigBench.N) workers(i) = system.spawn(Reactor[Cmd] { self =>
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
        case Start()  => doPing()
        case End() =>
          self.main.seal()
          responses.seal()
      }
    })
    for (i <- 0 until BigBench.N) workers(i) ! Start()

    assert(Await.result(done.future, Duration.Inf))
  }
}

object BigBench {
  // The number of workers to create.
  val N = 1280
}

/** CountingActor benchmark workload.
 *
 *  Motivated by the Savina Counting Actor benchmark.
 *
 *  Creates a counting worker, sends it a stream of increment messages,
 *  and then simply terminates with a message that asks the worker
 *  to report the total count.
 *
 *  Messages exchanged: sz (inc) + 1 (get)
 */
class CountingActor(val system: ReactorSystem) {
  trait Cmd
  case class Increment() extends Cmd
  case class Get() extends Cmd

  def run(sz: Int) = {
    val done = Promise[Int]()

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

    assert(Await.result(done.future, Duration.Inf) == sz)
  }
}

/** Fibonacci benchmark workload.
 *
 *  Motivated by the Savina Fibonacci benchmark.
 *
 *  Amazing how often people use an absolutely crazy algorithm to compute an absolutely useless result.
 *
 *  Messages exchanged: O(2 ^ sz)
 */
class Fibonacci(val system: ReactorSystem) {

  def run(sz: Int) = {
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

    Await.ready(done.future, Duration.Inf)
  }
}

/** ForkJoinCreation benchmark workload.
 *
 *  Motivated by the Savina Fork Join benchmark.
 *
 *  Creates a high number of workers that all terminate after a single message.
 *
 *  Messages exchanged: sz
 */
class ForkJoinCreation(val system: ReactorSystem) {

  def run(sz: Int) = {
    val done = new Array[Promise[Boolean]](sz)
    for (i <- 0 until sz) done(i) = Promise[Boolean]()

    val workers: Array[Channel[String]] = (for (i <- 0 until sz) yield {
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
      Await.result(done(i).future, Duration.Inf)
    }
  }
}

/** ForkJoinThroughput benchmark workload.
 *
 *  Motivated by the Savina Fork Join benchmark.
 *
 *  Creates a fixed number of workers that all terminate after processing a given number of messages.
 *
 *  Messages exchanged: K * sz
 */
class ForkJoinThroughput(val system: ReactorSystem) {

  def run(sz: Int) = {
    val done = new Array[Promise[Boolean]](ForkJoinThroughput.K)
    for (i <- 0 until ForkJoinThroughput.K) done(i) = Promise[Boolean]()

    val workers: Array[Channel[String]] = (for (i <- 0 until ForkJoinThroughput.K) yield {
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
        while (i < ForkJoinThroughput.K) {
          workers(i) ! "event"
          i += 1
        }
        j += 1
      }
    })

    for (i <- 0 until ForkJoinThroughput.K) {
      Await.result(done(i).future, Duration.Inf)
    }
  }
}

object ForkJoinThroughput {
  // The number of workers to create.
  val K = 256
}

/** PingPong benchmark workload.
 *
 *  Motivated by the Savina Ping Pong benchmark.
 *
 *  Creates a pair of workers that do sequential ping pong a given number of times.
 *
 *  Messages exchanged: 2 * sz (ping, pong)
 */
class PingPong(val system: ReactorSystem) {

  def run(sz: Int) {
    val done = Promise[Boolean]()

    // Inner class to handle circular reference between ping and pong.
    class PingPongInner {
      val ping: Channel[String] = system.spawn(Reactor { (self: Reactor[String]) =>
        val pong: Channel[String] = system.spawn(Reactor { (self: Reactor[String]) =>
          var left = sz
          self.main.events onEvent { x =>
            ping ! "pong"
            left -= 1
            if (left == 0) self.main.seal()
          }
        })
        var left = sz
        pong ! "ping"
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
    new PingPongInner

    Await.result(done.future, Duration.Inf)
  }
}

/** StreamingPingPong benchmark workload.
 *
 *  Motivated by the Savina Ping Pong benchmark.
 *
 *  Creates a pair of workers that do overlapping ping pong a given number of times.
 *
 *  Messages exchanged: 2 * sz (ping, pong)
 */
class StreamingPingPong(val system: ReactorSystem) {

  def run(sz: Int) {
    val done = Promise[Boolean]()

    // Inner class to handle circular reference between ping and pong.
    class PingPongInner {
      val ping: Channel[String] = system.spawn(Reactor { (self: Reactor[String]) =>
        val pong: Channel[String] = system.spawn(Reactor { (self: Reactor[String]) =>
          var left = sz
          self.main.events onEvent { x =>
            ping ! "pong"
            left -= 1
            if (left == 0) self.main.seal()
          }
        })
        var left = sz
        for (i <- 0 until StreamingPingPong.WINDOW_SIZE) pong ! "ping"
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
    new PingPongInner

    Await.result(done.future, Duration.Inf)
  }
}

object StreamingPingPong {
  // How many ping pong exchanges to overlap.
  val WINDOW_SIZE = 128
}

/** Roundabout benchmark workload.
 *
 *  Creates a worker that listens on many channels and sends a constant total number of messages round robin to all those channels.
 *
 *  Messages exchanged: N
 */
class Roundabout(val system: ReactorSystem) {

  def run(sz: Int) = {
    val done = Promise[Boolean]()

    val roundabout = system.spawn(Reactor[Channel[Array[Channel[Int]]]] { self =>
      val connectors = (for (i <- 0 until sz) yield {
        system.channels.open[Int]
      }).toArray
      var count = 0
      for (c <- connectors) c.events.on {
        count += 1
        if (count == Roundabout.N) {
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
        while (i < Roundabout.N) {
          chs(i % sz) ! i
          i += 1
        }
        self.main.seal()
      }
    })

    Await.result(done.future, Duration.Inf)
  }
}

object Roundabout {
  // How many messages to send.
  val N = 500000
}

/** ThreadRing benchmark workload.
 *
 *  Motivated by the Savina Thread Ring benchmark.
 *
 *  Creates a ring of workers that forward a message around.
 *
 *  Messages exchanged: sz (rounded to multiple of RING_SIZE)
 */
class ThreadRing(val system: ReactorSystem) {

  def run(sz: Int) {
    val done = Promise[Boolean]()

    // Inner class to handle references to ring array.
    class RingInner {
      val ring: Array[Channel[Int]] = (for (i <- 0 until ThreadRing.RING_SIZE) yield {
        system.spawn(Reactor[Int] { self =>
          var rounds = sz / ThreadRing.RING_SIZE
          self.main.events.onEvent { x =>
            rounds -= 1
            if (rounds == 0) {
              self.main.seal()
              if (i == ring.length - 1) done.success(true)
            }
            ring((i + 1) % ring.length) ! x
          }
        })
      }).toArray
      ring(0) ! 666
    }
    new RingInner

    Await.result(done.future, Duration.Inf)
  }
}

object ThreadRing {
  // Size of worker ring.
  val RING_SIZE = 1000
}
