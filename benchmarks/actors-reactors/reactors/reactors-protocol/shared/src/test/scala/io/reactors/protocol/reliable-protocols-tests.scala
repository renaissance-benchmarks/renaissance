package io.reactors.protocol



import io.reactors._
import io.reactors.protocol.instrument.Scripted
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.collection.mutable
import scala.concurrent.ExecutionContext
import scala.concurrent.Promise
import scala.concurrent.duration._
import org.scalatest.funsuite.AsyncFunSuite



class ReliableProtocolsSpec extends AsyncFunSuite with AsyncTimeLimitedTests {
  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("open a reliable channel and receive an event") {
    val system = ReactorSystem.default("conversions", Scripted.defaultBundle)
    val done = Promise[Boolean]

    system.spawnLocal[Unit] { self =>
      val server = system.channels.daemon.reliableServer[String]
        .serveReliable(Reliable.Policy.reorder(128))

      server.links onEvent { link =>
        link.events onMatch {
          case "finish" =>
            done.success(true)
            self.main.seal()
        }
      }

      server.channel.openReliable(Reliable.Policy.reorder(128)) onEvent { reliable =>
        reliable.channel ! "finish"
      }
    }

    done.future.map(t => assert(t))
  }

  test("restore proper order when the underlying channel reorders events") {
    val system = ReactorSystem.default("conversions", Scripted.defaultBundle)
    val event1 = Promise[String]
    val event2 = Promise[String]

    val policy = Reliable.Policy.reorder(128)
    system.channels.registerTemplate(TwoWay.OutputTag, system.channels.named("out"))

    val proto = Reactor.reliableServer[String](policy) { server =>
      server.links onEvent { link =>
        link.events onEvent { x =>
          if (!event1.trySuccess(x)) {
            event2.success(x)
            server.subscription.unsubscribe()
          }
        }
      }
    }
    val server = system.spawn(proto.withName("server"))

    system.spawnLocal[Unit] { self =>
      server.openReliable(policy) onEvent { r =>
        val twoWayOut = self.system.channels.get[Stamp[String]]("server", "out").get
        self.system.service[Scripted].instrument(twoWayOut) {
          _.take(2).reverse
        }
        r.channel ! "first"
        r.channel ! "second"
      }
    }

    val done = for {
      x <- event1.future
      y <- event2.future
    } yield (x, y)
    done.map(t => assert(t == ("first", "second")))
  }

  test("restore proper order when acknowledgements are delayed") {
    val system = ReactorSystem.default("conversions", Scripted.defaultBundle)
    val done = Promise[Seq[Int]]()

    val total = 256
    val window = total / 2
    val policy = Reliable.Policy.reorder(window)
    system.channels.registerTemplate(TwoWay.InputTag, system.channels.named("acks"))

    val server = system.reliableServer[Int](policy) { server =>
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

    val proto = Reactor[Unit] { self =>
      server.openReliable(policy) onEvent { r =>
        val acks = self.system.channels.get[Long]("client", "acks").get
        self.system.service[Scripted].instrument(acks) {
          _.take(window).throttle(_ => 10.millis)
        }
        for (i <- 0 until total) {
          r.channel ! i
        }
      }
    }
    system.spawn(proto.withName("client"))

    done.future.map(t => assert(t == (0 until total)))
  }

  test("restore proper order when second event is delayed for a long amount of time") {
    val system = ReactorSystem.default("conversions", Scripted.defaultBundle)
    val done = Promise[Seq[Int]]()
    val total = 16
    val policy = Reliable.Policy.reorder(4)
    system.channels.registerTemplate(TwoWay.OutputTag, system.channels.named("out"))

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
        val out = system.channels.get[Stamp[Int]]("server", "out").get
        system.service[Scripted].instrument(out) {
          events => events.take(2).throttle(_ => 2.seconds)
        }

        for (i <- 0 until total) r.channel ! i
      }
    }

    done.future.map(t => assert(t == (0 until total)))
  }

  test("restore proper order in a two way reliable channel") {
    val system = ReactorSystem.default("conversions", Scripted.defaultBundle)
    val done = Promise[Seq[String]]()
    val total = 64
    val policy = Reliable.TwoWay.Policy.reorder(16)
    system.channels.registerTemplate(TwoWay.OutputTag, system.channels.named("out"))

    val serverProto = Reactor.reliableTwoWayServer[String, Int](policy) { server =>
      server.links onEvent { twoWay =>
        twoWay.input onEvent { n =>
          twoWay.output ! n.toString
        }
      }
    }
    val server = system.spawn(serverProto.withName("server"))

    val clientProto = Reactor[Unit] { self =>
      server.connectReliable(policy) onEvent { twoWay =>
        val clientOut = system.channels.get[Stamp[Int]]("client", "out").get
        val serverOut = system.channels.get[Stamp[Int]]("server", "out").get
        system.service[Scripted].instrument(clientOut) {
          events => events.take(3).reverse.throttle(_ => 1.second)
        }
        system.service[Scripted].instrument(serverOut) {
          events => events.take(4).reverse.throttle(_ => 1.second)
        }

        for (i <- 0 until total) twoWay.output ! i
        val seen = mutable.Buffer[String]()
        twoWay.input onEvent { s =>
          seen += s
          if (s == (total - 1).toString) {
            done.success(seen)
          }
        }
      }
    }
    system.spawn(clientProto.withName("client"))

    done.future.map(t => assert(t == (0 until total).map(_.toString)))
  }
}
