package io.reactors
package protocol



import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import scala.collection._
import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration._



class BackpressureProtocolsCheck
extends Properties("BackpressureProtocolsCheck") with ExtendedProperties {
  val sizes = detChoose(1, 256)

  def producerConsumer[R: Arrayable](
    total: Int,
    window: Int,
    system: ReactorSystem,
    medium: Backpressure.Medium[R, Int],
    policy: Backpressure.Policy
  ): Promise[Seq[Int]] = {
    val done = Promise[Seq[Int]]()

    val server = system.spawnLocal[R] { self =>
      val pumpServer = self.main.serveBackpressure(medium, policy)
      pumpServer.links onEvent { pump =>
        val seen = mutable.Buffer[Int]()
        pump.buffer.available.is(true) on {
          assert(pump.buffer.size <= window)
          while (pump.buffer.available()) {
            val x = pump.buffer.dequeue()
            seen += x
            if (x == (total - 1)) {
              done.success(seen)
              pumpServer.subscription.unsubscribe()
            }
          }
        }
      }
    }

    system.spawnLocal[Unit] { self =>
      server.openBackpressure(medium, policy) onEvent { valve =>
        var i = 0
        valve.available.is(true) on {
          while (valve.available() && i < total) {
            valve.channel ! i
            i += 1
          }
        }
      }
    }

    done
  }

  property("batching backpressure on default medium") = forAllNoShrink(sizes, sizes) {
    (total, window) =>
    stackTraced {
      val system = ReactorSystem.default("check-system")
      val medium = Backpressure.Medium.default[Int]
      val policy = Backpressure.Policy.batching(window)

      val done = producerConsumer(total, window, system, medium, policy)

      assert(Await.result(done.future, 5.seconds) == (0 until total))
      system.shutdown()
      true
    }
  }

  property("batching backpressure on reliable medium") = forAllNoShrink(sizes, sizes) {
    (total, window) =>
      stackTraced {
        val system = ReactorSystem.default("test system")
        val medium =
          Backpressure.Medium.reliable[Int](Reliable.TwoWay.Policy.reorder(window))
        val policy = Backpressure.Policy.batching(window)

        val done = producerConsumer(total, window, system, medium, policy)

        assert(Await.result(done.future, 5.seconds) == (0 until total))
        system.shutdown()
        true
      }
  }

  property("sliding backpressure on reliable medium") = forAllNoShrink(sizes, sizes) {
    (total, window) =>
    stackTraced {
      val system = ReactorSystem.default("test system")
      val medium =
        Backpressure.Medium.reliable[Int](Reliable.TwoWay.Policy.reorder(window))
      val policy = Backpressure.Policy.sliding(window)

      val done = producerConsumer(total, window, system, medium, policy)

      assert(Await.result(done.future, 5.seconds) == (0 until total))
      system.shutdown()
      true
    }
  }
}
