package io.reactors
package protocol



import io.reactors.common.Conc
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.collection._
import scala.concurrent.ExecutionContext
import scala.concurrent.Future
import scala.concurrent.Promise
import scala.concurrent.duration._
import org.scalatest.funsuite.AsyncFunSuite



class StreamingLibraryTest extends AsyncFunSuite with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("streaming-lib")

  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  import StreamingLibraryTest._

  test("streaming filter, map and batch") {
    val total = 4096
    val done = Promise[Seq[Seq[Int]]]()

    system.spawnLocal[Unit] { self =>
      val seen = mutable.Buffer[Seq[Int]]()
      val source = new Source[Int](system)
      val ready = source.filter(_ % 2 == 0).map(_ * 2).batch(2).foreach { xs =>
        seen += xs
        if (seen.size == total / 4) done.success(seen)
      }

      ready on {
        var i = 0
        source.valve.available.is(true) on {
          while (source.valve.available() && i < total) {
            source.valve.channel ! i
            i += 1
          }
        }
      }
    }

    val expected = (0 until total).filter(_ % 2 == 0).map(_ * 2).grouped(2).toSeq
    done.future.map(t => assert(t == expected))
  }

  test("streaming scanPast") {
    val total = 4096
    val done = Promise[Seq[Long]]()

    system.spawnLocal[Unit] { self =>
      val seen = mutable.Buffer[Long]()
      val source = new Source[Int](system)
      val ready = source.scanPast(0L)(_ + _).foreach { x =>
        seen += x
        if (seen.size == total) done.success(seen)
      }

      ready on {
        var i = 0
        source.valve.available.is(true) on {
          while (source.valve.available() && i < total) {
            source.valve.channel ! i
            i += 1
          }
        }
      }
    }

    val expected = (0 until total).map(_.toLong).scanLeft(0L)(_ + _).tail
    done.future.map(t => assert(t == expected))
  }
}


object StreamingLibraryTest {
  type StreamReq[T] = Channel[Reliable.TwoWay.Req[Int, T]]

  type StreamServer[T] = Channel[StreamReq[T]]

  type StreamMedium[T] = Backpressure.Medium[Reliable.TwoWay.Req[Int, T], T]

  trait Stream[T] {
    def system: ReactorSystem

    def streamServer: StreamServer[T]

    def backpressureMedium[R: Arrayable]: StreamMedium[R]

    def backpressurePolicy: Backpressure.Policy

    def map[S](f: T => S)(implicit at: Arrayable[T], as: Arrayable[S]): Stream[S] =
      new Mapped(this, f)

    def filter(p: T => Boolean)(implicit at: Arrayable[T]): Stream[T] =
      new Filtered(this, p)

    def batch(size: Int)(implicit at: Arrayable[T]): Stream[Seq[T]] =
      new Batch(this, size)

    def scanPast[S](z: S)(op: (S, T) => S)(
      implicit at: Arrayable[T], as: Arrayable[S]
    ): Stream[S] = new ScanPast(this, z, op)

    def sliding(size: Int)(implicit at: Arrayable[T]): Stream[Conc.Queue[T]] =
      new Sliding(this, size)

    def foreach(f: T => Unit)(implicit a: Arrayable[T]): IVar[Unit] = {
      val medium = backpressureMedium[T]
      val policy = backpressurePolicy
      val server = system.channels.backpressureServer(medium)
        .serveBackpressure(medium, policy)
      streamServer ! server.channel
      val incoming = server.links.once
      incoming onEvent { pump =>
        pump.buffer.onEvent(f)
        pump.buffer.available.is(true) on {
          while (pump.buffer.nonEmpty) pump.buffer.dequeue()
        }
      }
      incoming.once.map(_ => ()).toIVar
    }
  }

  class Source[T: Arrayable](val system: ReactorSystem) extends Stream[T] {
    def backpressureMedium[R: Arrayable] =
      Backpressure.Medium.reliable[R](Reliable.TwoWay.Policy.reorder(256))

    val backpressurePolicy = Backpressure.Policy.sliding(256)

    val (valve, streamServer) = {
      val multi = new MultiValve[T](256)

      val server = system.channels.open[StreamReq[T]]
      server.events.onEvent { bs =>
        bs.openBackpressure(backpressureMedium[T], backpressurePolicy) onEvent { v =>
          multi += v
        }
      }

      (multi.out, server.channel)
    }
  }

  trait Transformed[T, S] extends Stream[S] {
    implicit val arrayableT: Arrayable[T]

    implicit val arrayableS: Arrayable[S]

    def backpressureMedium[R: Arrayable] = parent.backpressureMedium[R]

    val backpressurePolicy = parent.backpressurePolicy

    def parent: Stream[T]

    def kernel(x: T, output: Channel[S]): Unit

    val streamServer: StreamServer[S] = {
      val inMedium = backpressureMedium[T]
      val outMedium = backpressureMedium[S]
      val policy = backpressurePolicy

      system.spawn(Reactor[StreamReq[S]] { self =>
        val multi = new MultiValve[S](256)
        val server = self.system.channels.backpressureServer(inMedium)
          .serveBackpressureConnections(inMedium, policy)
        parent.streamServer ! server.channel

        val incoming = server.links.once
        incoming onEvent { c =>
          val available = (c.buffer.available zip multi.out.available)(_ && _)
            .changes.toSignal(false)
          available.is(true) on {
            while (available()) {
              val x = c.buffer.dequeue()
              kernel(x, multi.out.channel)
              c.pressure ! 1
            }
          }
        }

        self.main.events.defer(incoming) onEvent { backServer =>
          backServer.openBackpressure(outMedium, policy) onEvent {
            valve => multi += valve
          }
        }
      })
    }
  }

  class Mapped[T, S](val parent: Stream[T], val f: T => S)(
    implicit val arrayableT: Arrayable[T], val arrayableS: Arrayable[S]
  ) extends Transformed[T, S] {
    lazy val system = parent.system

    def kernel(x: T, output: Channel[S]): Unit = {
      val y = f(x)
      output ! y
    }
  }

  class Filtered[T](val parent: Stream[T], val p: T => Boolean)(
    implicit val arrayableT: Arrayable[T], val arrayableS: Arrayable[T]
  ) extends Transformed[T, T] {
    lazy val system = parent.system

    def kernel(x: T, output: Channel[T]): Unit = {
      if (p(x)) output ! x
    }
  }

  class Batch[T](val parent: Stream[T], val limit: Int)(
    implicit val arrayableT: Arrayable[T], val arrayableS: Arrayable[Seq[T]]
  ) extends Transformed[T, Seq[T]] {
    lazy val system = parent.system
    var buffer = mutable.Buffer[T]()

    def kernel(x: T, output: Channel[Seq[T]]): Unit = {
      buffer += x
      if (buffer.size == limit) {
        output ! buffer
        buffer = mutable.Buffer[T]()
      }
    }
  }

  class Sliding[T](val parent: Stream[T], val limit: Int)(
    implicit val arrayableT: Arrayable[T], val arrayableS: Arrayable[Conc.Queue[T]]
  ) extends Transformed[T, Conc.Queue[T]] {
    lazy val system = parent.system
    var queue = new Conc.Queue[T]

    def kernel(x: T, output: Channel[Conc.Queue[T]]): Unit = {
      queue = queue.enqueue(x)
      if (queue.size > limit) queue = queue.dequeue()
      output ! queue
    }
  }

  class ScanPast[T, S](val parent: Stream[T], val z: S, op: (S, T) => S)(
    implicit val arrayableT: Arrayable[T], val arrayableS: Arrayable[S]
  ) extends Transformed[T, S] {
    lazy val system = parent.system
    var last: S = z

    def kernel(x: T, output: Channel[S]): Unit = {
      last = op(last, x)
      output ! last
    }
  }
}
