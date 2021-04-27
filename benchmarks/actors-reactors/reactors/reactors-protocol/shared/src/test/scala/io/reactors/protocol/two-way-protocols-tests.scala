package io.reactors
package protocol



import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.concurrent.Promise
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import org.scalatest.funsuite.AsyncFunSuite



class TwoWayProtocolsSpec extends AsyncFunSuite with AsyncTimeLimitedTests {
  val system = ReactorSystem.default("conversions")

  def timeLimit = 10.seconds

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("open two-way server, connect and send event") {
    val done = Promise[String]()
    val proto = Reactor[Unit] { self =>
      val server = system.channels.daemon.twoWayServer[Unit, String].serveTwoWay()

      server.links.onEvent { twoWay =>
        twoWay.input onEvent { s =>
          done.success(s)
          self.main.seal()
        }
      }

      server.channel.connect() onEvent { twoWay =>
        twoWay.output ! "2-way"
      }
    }
    system.spawn(proto)
    done.future.map(s => assert(s == "2-way"))
  }

  test("open two-way server, connect, send event, await reply") {
    val done = Promise[Int]()
    val proto = Reactor[Unit] { self =>
      val server = system.channels.daemon.twoWayServer[Int, String].serveTwoWay()

      server.links.onEvent { twoWay =>
        twoWay.input onEvent { s =>
          twoWay.output ! s.length
        }
      }

      server.channel.connect() onEvent { twoWay =>
        twoWay.output ! "how-long"
        twoWay.input onEvent { len =>
          done.success(len)
          self.main.seal()
        }
      }
    }
    system.spawn(proto)
    done.future.map(len => assert(len == 8))
  }

  test("open a two-way server and ping-pong-count up to 10") {
    val done = Promise[Int]
    val proto = Reactor[Unit] { self =>
      val server = system.channels.daemon.twoWayServer[Int, Int].serveTwoWay()

      server.links.onEvent { twoWay =>
        twoWay.input onEvent { n =>
          twoWay.output ! n
        }
      }

      server.channel.connect() onEvent { twoWay =>
        twoWay.output ! 0
        var sum = 0
        twoWay.input onEvent { n =>
          sum += n
          if (n < 10) {
            twoWay.output ! n + 1
          } else {
            done.success(sum)
            self.main.seal()
          }
        }
      }
    }
    system.spawn(proto)
    done.future.map(n => assert(n == 55))
  }

  test("open a two-way server reactor and connect to it from another reactor") {
    val done = Promise[String]

    val server = system.twoWayServer[String, Int] { server =>
      server.links onEvent { twoWay =>
        twoWay.input onEvent { n =>
          twoWay.output ! n.toString
        }
      }
    }

    system.spawnLocal[Unit] { self =>
      server.connect() onEvent { twoWay =>
        twoWay.output ! 7
        twoWay.input onEvent { s =>
          done.success(s)
          self.main.seal()
        }
      }
    }

    done.future.map(s => assert(s == "7"))
  }

  test("server unsubscribes after the first event, does not receive the second") {
    val done = Promise[String]

    val server = system.twoWayServer[String, Int] { server =>
      server.links onEvent { twoWay =>
        var first = true
        twoWay.input onEvent { x =>
          if (first) {
            assert(x == 7)
            twoWay.subscription.unsubscribe()
            server.subscription.unsubscribe()
            first = false
          } else {
            done.success("Got second event!")
          }
        }
      }

      Reactor.self.sysEvents onMatch {
        case ReactorTerminated =>
          done.success("terminated")
      }
    }

    system.spawnLocal[Unit] { self =>
      server.connect() onEvent { twoWay =>
        twoWay.output ! 7
        twoWay.output ! 11
        self.main.seal()
      }
    }

    done.future.map(s => assert(s == "terminated"))
  }

  test("client unsubscribes after the first event, does not receive the second") {
    val done = Promise[String]

    val serverProto = Reactor.twoWayServer[String, Int] { server =>
      server.links onEvent { twoWay =>
        twoWay.input onEvent { x =>
          twoWay.output ! x.toString
          twoWay.output ! "second event that you should not see"
          server.subscription.unsubscribe()
        }
      }
    }
    val server = system.spawn(serverProto)

    system.spawnLocal[Unit] { self =>
      var reply = ""
      server.connect() onEvent { twoWay =>
        twoWay.output ! 11
        twoWay.input onEvent { txt =>
          reply = txt
          twoWay.subscription.unsubscribe()
          self.main.seal()
        }
      }

      self.sysEvents onMatch {
        case ReactorTerminated => done.success(reply)
      }
    }

    done.future.map(s => assert(s == "11"))
  }
}
