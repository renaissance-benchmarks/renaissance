package io.reactors
package protocol



import io.reactors.protocol.instrument.Scripted
import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import scala.collection.mutable
import scala.concurrent._
import scala.concurrent.duration._



class ReliableProtocolsCheck
extends Properties("BackpressureProtocolsCheck") with ExtendedProperties {
  val sizes = detChoose(1, 256)
  val windows = detChoose(1, 256)
  val delayCounts = detChoose(1, 256)

  property("restore proper order") = forAllNoShrink(sizes, windows, delayCounts) {
    (total, window, randomDelayCount) =>
    stackTraced {
      val delayCount = math.min(randomDelayCount, math.min(total, window))
      val done = Promise[Seq[Int]]()
      val system = ReactorSystem.default("check-system", Scripted.defaultBundle)

      system.channels.registerTemplate(TwoWay.OutputTag, system.channels.named("out"))

      val policy = Reliable.Policy.reorder(window)
      val proto = Reactor.reliableServer[Int](policy) { server =>
        server.links onEvent { link =>
          val seen = mutable.Buffer[Int]()
          link.events onEvent { x =>
            seen += x
            if (x == total - 1) {
              done.success(seen)
            }
          }
        }
      }
      val server = system.spawn(proto.withName("server"))

      system.spawnLocal[Unit] { self =>
        server.openReliable(policy) onEvent { r =>
          val twoWayOut = self.system.channels.get[Stamp[String]]("server", "out").get
          self.system.service[Scripted].instrument(twoWayOut) {
            _.take(delayCount).reverse
          }
          for (i <- 0 until total) r.channel ! i
        }
      }

      assert(Await.result(done.future, 10.seconds) == (0 until total))
      true
    }
  }
}
