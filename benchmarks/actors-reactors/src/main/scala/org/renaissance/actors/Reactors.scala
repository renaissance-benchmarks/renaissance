package org.renaissance.actors

import io.reactors.Channel
import io.reactors.Reactor
import io.reactors.ReactorPreempted
import io.reactors.ReactorSystem
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration._
import scala.util.Random

@Name("reactors")
@Group("concurrency")
@Group("actors")
@Summary(
  "Runs benchmarks inspired by the Savina microbenchmark workloads in a sequence on Reactors.IO."
)
@Licenses(Array(License.MIT))
@Repetitions(10)
@Parameter(name = "scaling_factor", defaultValue = "1.0")
@Configuration(name = "test", settings = Array("scaling_factor = 0.1"))
@Configuration(name = "jmh")
final class Reactors extends Benchmark {

  // Code based on https://github.com/reactors-io/reactors
  // The original uses BSD 3-clause license, the result is compatible with MIT license.

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var scalingFactorParam: Double = _

  private var system: ReactorSystem = _

  private var expectedFibonacci: Int = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    scalingFactorParam = c.parameter("scaling_factor").toDouble

    // Instantiate the default reactor system used throughout the benchmark.
    system = ReactorSystem.default("bench-system")
    expectedFibonacci = Fibonacci.computeExpected((28 * scalingFactorParam).intValue())
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    // Shut down the reactor system.
    system.shutdown()
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {

    // TODO: Address workload scaling. One option is to tune dimensions so that each workload sends roughly equal number of messages.

    // TODO: The use of scaling factor is not strictly correct with Fibonacci and Roundabout. For these benchmarks, the work done is not a linear function of the input argument.

    Validators.compound(
      Baseline.run(system, (1000000 * scalingFactorParam).intValue()),
      BigBench.run(system, (4000 * scalingFactorParam).intValue()),
      CountingActor.run(system, (8000000 * scalingFactorParam).intValue()),
      Fibonacci.run(system, (28 * scalingFactorParam).intValue(), expectedFibonacci),
      ForkJoinCreation.run(system, (250000 * scalingFactorParam).intValue()),
      ForkJoinThroughput.run(system, (21000 * scalingFactorParam).intValue()),
      PingPong.run(system, (1500000 * scalingFactorParam).intValue()),
      StreamingPingPong.run(system, (5000000 * scalingFactorParam).intValue()),
      Roundabout.run(system, (750000 * scalingFactorParam).intValue()),
      ThreadRing.run(system, (2500000 * scalingFactorParam).intValue())
    )
  }
}

/**
 * Baseline benchmark workload.
 *
 *  Exercise the basic reactor scheduler functionality.
 *  Wait for the system event stream to indicate that the reactor is no longer scheduled,
 *  and send a new message to the main event stream to schedule the reactor in response.
 *
 *  Messages exchanged: sz
 */
private object Baseline {

  def run(system: ReactorSystem, sz: Int) = {
    println("Baseline workload: Reactor scheduling events")

    val done = Promise[Int]()

    system.spawn(Reactor[String] { self =>
      var left = sz
      self.sysEvents onMatch {
        case ReactorPreempted =>
          self.main.channel ! "more"
      }
      self.main.events onEvent { _ =>
        left -= 1
        if (left == 0) {
          done.success(left)
          self.main.seal()
        }
      }
    })

    Validators.simple("Baseline", 0, Await.result(done.future, Duration.Inf).longValue)
  }
}

/**
 * BigBench benchmark workload.
 *
 *  Motivated by the Savina Big benchmark.
 *
 *  Creates a constant number of workers, each with two channels, one for requests, one for responses.
 *  Once started, each worker picks another at random, sends it a ping, and waits for a pong in response.
 *
 *  Messages exchanged: 2 * N * sz (ping, pong) + 2 * N (start, end)
 */
private object BigBench {

  // The number of workers to create.
  val NUM_WORKERS = 1280

  trait Cmd
  case class Ping(ch: Channel[String]) extends Cmd
  case class Start() extends Cmd
  case class End() extends Cmd

  def run(system: ReactorSystem, sz: Int) = {
    println("BigBench workload: Many-to-many message ping pong")

    val done = Promise[Int]()
    val workers = new Array[Channel[Cmd]](BigBench.NUM_WORKERS)

    // Coordinator reactor. Responsible for reaping workers at the end of the workload.
    val sink = system.spawn(Reactor[String] { self =>
      var left = BigBench.NUM_WORKERS
      self.main.events.on {
        left -= 1
        if (left == 0) {
          for (i <- 0 until BigBench.NUM_WORKERS) workers(i) ! End()
          done.success(left)
          self.main.seal()
        }
      }
    })

    // Worker reactors. Responsible for pinging and ponging.
    for (i <- 0 until BigBench.NUM_WORKERS) workers(i) = system.spawn(Reactor[Cmd] { self =>
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
    for (i <- 0 until BigBench.NUM_WORKERS) workers(i) ! Start()

    Validators.simple("BigBench", 0, Await.result(done.future, Duration.Inf).longValue)
  }
}

/**
 * CountingActor benchmark workload.
 *
 *  Motivated by the Savina Counting Actor benchmark.
 *
 *  Creates a counting worker, sends it a stream of increment messages,
 *  and then simply terminates with a message that asks the worker
 *  to report the total count.
 *
 *  Messages exchanged: sz (inc) + 1 (get)
 */
private object CountingActor {
  trait Cmd
  case class Increment() extends Cmd
  case class Get() extends Cmd

  def run(system: ReactorSystem, sz: Int) = {
    println("CountingActor workload: Single reactor event processing")

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

    system.spawn(Reactor[Unit] { self =>
      val inc = new Increment
      var i = 0
      while (i < sz) {
        counting ! inc
        i += 1
      }
      counting ! Get()
      self.main.seal()
    })

    Validators.simple(
      "CountingActor",
      sz,
      Await.result(done.future, Duration.Inf).longValue
    )
  }
}

/**
 * Fibonacci benchmark workload.
 *
 *  Motivated by the Savina Fibonacci benchmark.
 *
 *  Amazing how often people use an absolutely crazy algorithm to compute an absolutely useless result.
 *
 *  Messages exchanged: O(2 ** sz)
 */
object Fibonacci {

  def run(system: ReactorSystem, sz: Int, exp: Int): BenchmarkResult = {
    println("Fibonacci workload: Dynamic reactor mix with varying lifetimes")

    val done = Promise[Int]()

    def fib(parent: Channel[Int], n: Int): Unit = {
      system.spawn(Reactor[Int] { self =>
        n match {
          case 0 =>
            parent ! 0
            self.main.seal()
          case 1 =>
            parent ! 1
            self.main.seal()
          case _ =>
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

    Validators.simple("Fibonacci", exp, Await.result(done.future, Duration.Inf).longValue)
  }

  def computeExpected(sz: Int): Int = {
    @annotation.tailrec
    def computeWithTail(n: Int, one: Int, two: Int): Int = {
      n match {
        case 0 => one
        case _ => computeWithTail(n - 1, two, one + two)
      }
    }
    computeWithTail(sz, 0, 1)
  }
}

/**
 * ForkJoinCreation benchmark workload.
 *
 *  Motivated by the Savina Fork Join benchmark.
 *
 *  Creates a high number of workers that all terminate after a single message.
 *
 *  Messages exchanged: sz
 */
private object ForkJoinCreation {

  def run(system: ReactorSystem, sz: Int) = {
    println("ForkJoinCreation workload: Reactor creation performance")

    val done = new Array[Promise[Int]](sz)
    for (i <- 0 until sz) done(i) = Promise[Int]()

    val workers: Array[Channel[String]] = (for (i <- 0 until sz) yield {
      system.spawn(Reactor[String] { self =>
        self.main.events.on {
          done(i).success(1)
          self.main.seal()
        }
      })
    }).toArray

    var i = 0
    while (i < sz) {
      workers(i) ! "event"
      i += 1
    }

    var res: Int = 0
    for (i <- 0 until sz) {
      res += Await.result(done(i).future, Duration.Inf)
    }

    Validators.simple("ForkJoinCreation", sz, res)
  }
}

/**
 * ForkJoinThroughput benchmark workload.
 *
 *  Motivated by the Savina Fork Join benchmark.
 *
 *  Creates a fixed number of workers that all terminate after processing a given number of messages.
 *
 *  Messages exchanged: K * sz
 */
private object ForkJoinThroughput {

  // The number of workers to create.
  val NUM_WORKERS = 256

  def run(system: ReactorSystem, sz: Int) = {
    println("ForkJoinThroughput workload: Reactor processing performance")

    val done = new Array[Promise[Int]](ForkJoinThroughput.NUM_WORKERS)
    for (i <- 0 until ForkJoinThroughput.NUM_WORKERS) done(i) = Promise[Int]()

    val workers: Array[Channel[String]] =
      (for (i <- 0 until ForkJoinThroughput.NUM_WORKERS) yield {
        system.spawn(Reactor[String] { self =>
          var count = 0
          self.main.events.on {
            count += 1
            if (count == sz) {
              done(i).success(count)
              self.main.seal()
            }
          }
        })
      }).toArray

    system.spawn(Reactor[String] { _ =>
      var j = 0
      while (j < sz) {
        var i = 0
        while (i < ForkJoinThroughput.NUM_WORKERS) {
          workers(i) ! "event"
          i += 1
        }
        j += 1
      }
    })

    var res: Int = 0
    for (i <- 0 until ForkJoinThroughput.NUM_WORKERS) {
      res += Await.result(done(i).future, Duration.Inf)
    }

    Validators.simple("ForkJoinThroughput", ForkJoinThroughput.NUM_WORKERS * sz, res)
  }
}

/**
 * PingPong benchmark workload.
 *
 *  Motivated by the Savina Ping Pong benchmark.
 *
 *  Creates a pair of workers that do sequential ping pong a given number of times.
 *
 *  Messages exchanged: 2 * sz (ping, pong)
 */
private object PingPong {

  def run(system: ReactorSystem, sz: Int) = {
    println("PingPong workload: Reactor pair sequential ping pong performance")

    val done = Promise[Int]()

    // Inner class to handle circular reference between ping and pong.
    class PingPongInner {
      val ping: Channel[String] = system.spawn(Reactor { self: Reactor[String] =>
        var left = sz
        self.main.events onEvent { _ =>
          left -= 1
          if (left > 0) {
            pong ! "ping"
          } else {
            done.success(left)
            self.main.seal()
          }
        }
      })

      val pong: Channel[String] = system.spawn(Reactor { self: Reactor[String] =>
        var left = sz
        self.main.events onEvent { _ =>
          left -= 1
          if (left == 0) {
            self.main.seal()
          }

          ping ! "pong"
        }
      })
    }

    val pair = new PingPongInner
    pair.pong ! "serve"

    Validators.simple("PingPong", 0, Await.result(done.future, Duration.Inf).longValue())
  }
}

/**
 * StreamingPingPong benchmark workload.
 *
 *  Motivated by the Savina Ping Pong benchmark.
 *
 *  Creates a pair of workers that do overlapping ping pong a given number of times.
 *
 *  Messages exchanged: 2 * sz (ping, pong)
 */
private object StreamingPingPong {

  // How many ping pong exchanges to overlap.
  val WINDOW_SIZE = 128

  def run(system: ReactorSystem, sz: Int) = {
    println("StreamingPingPong workload: Reactor pair overlapping ping pong performance")

    val done = Promise[Int]()

    // Inner class to handle circular reference between ping and pong.
    class PingPongInner {
      val ping: Channel[String] = system.spawn(Reactor { self: Reactor[String] =>
        var left = sz
        self.main.events onEvent { _ =>
          left -= 1
          if (left > 0) {
            pong ! "ping"
          } else {
            done.success(left)
            self.main.seal()
          }
        }
      })

      val pong: Channel[String] = system.spawn(Reactor { self: Reactor[String] =>
        var left = sz
        self.main.events onEvent { _ =>
          left -= 1
          if (left == 0) {
            self.main.seal()
          }

          ping ! "pong"
        }
      })
    }

    val pair = new PingPongInner
    for (_ <- 0 until StreamingPingPong.WINDOW_SIZE) {
      pair.pong ! "serve"
    }

    Validators.simple(
      "StreamingPingPong",
      0,
      Await.result(done.future, Duration.Inf).longValue
    )
  }
}

/**
 * Roundabout benchmark workload.
 *
 *  Creates a worker that listens on many channels and sends a constant total number of messages round robin to all those channels.
 *
 *  Messages exchanged: N
 */
private object Roundabout {

  // How many messages to send.
  val NUM_MESSAGES = 500000

  def run(system: ReactorSystem, sz: Int) = {
    println("Roundabout workload: Many channels reactor performance")

    val done = Promise[Int]()

    val roundabout = system.spawn(Reactor[Channel[Array[Channel[Int]]]] { self =>
      val connectors = (for (_ <- 0 until sz) yield {
        system.channels.open[Int]
      }).toArray
      var count = 0
      for (c <- connectors) c.events.on {
        count += 1
        if (count == Roundabout.NUM_MESSAGES) {
          connectors.foreach(_.seal())
          done.success(count)
        }
      }
      self.main.events.onEvent { ch =>
        ch ! connectors.map(_.channel)
        self.main.seal()
      }
    })

    val roundRobinDistributor = system.spawn(Reactor[Array[Channel[Int]]] { self =>
      self.main.events.onEvent { chs =>
        var i = 0
        while (i < Roundabout.NUM_MESSAGES) {
          chs(i % sz) ! i
          i += 1
        }
        self.main.seal()
      }
    })

    roundabout ! roundRobinDistributor

    Validators.simple(
      "Roundabout",
      Roundabout.NUM_MESSAGES,
      Await.result(done.future, Duration.Inf).longValue
    )
  }
}

/**
 * ThreadRing benchmark workload.
 *
 *  Motivated by the Savina Thread Ring benchmark.
 *
 *  Creates a ring of workers that forward a message around.
 *
 *  Messages exchanged: sz (rounded to multiple of RING_SIZE)
 */
private object ThreadRing {

  // Size of worker ring.
  val RING_SIZE = 1000

  def run(system: ReactorSystem, sz: Int) = {
    println("ThreadRing workload: Reactor ring forwarding performance")

    val done = Promise[Int]()

    // Inner class to handle references to ring array.
    class RingInner {
      val ring: Array[Channel[Int]] = (for (i <- 0 until ThreadRing.RING_SIZE) yield {
        system.spawn(Reactor[Int] { self =>
          var rounds = sz / ThreadRing.RING_SIZE
          self.main.events.onEvent { x =>
            rounds -= 1
            if (rounds == 0) {
              self.main.seal()
              if (i == ring.length - 1) done.success(rounds)
            }
            ring((i + 1) % ring.length) ! x
          }
        })
      }).toArray
    }

    val ring = new RingInner
    ring.ring(0) ! 666

    Validators.simple("ThreadRing", 0, Await.result(done.future, Duration.Inf).longValue)
  }
}
