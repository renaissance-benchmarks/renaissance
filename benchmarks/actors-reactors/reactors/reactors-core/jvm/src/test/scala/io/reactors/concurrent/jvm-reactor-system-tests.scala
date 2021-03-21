package io.reactors
package concurrent



import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Gen.choose
import scala.annotation.unchecked
import scala.collection._
import scala.concurrent.Await
import scala.concurrent.ExecutionContext.Implicits._
import scala.concurrent.Future
import scala.concurrent.Promise
import scala.concurrent.duration._
import scala.util.Success
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers



class PiggyReactor(val p: Promise[Boolean]) extends Reactor[Unit] {
  sysEvents onMatch {
    case ReactorStarted =>
      try {
        val piggy = JvmScheduler.Key.piggyback
        system.spawn(Proto[SelfReactor].withScheduler(piggy))
      } catch {
        case e: IllegalStateException =>
          p.success(true)
      } finally {
        main.seal()
      }
  }
}


class CtorExceptionReactor(val p: Promise[(Boolean, Boolean)])
extends Reactor[Unit] {
  var excepted = false
  var terminated = false
  sysEvents onMatch {
    case ReactorDied(t) =>
      excepted = true
    case ReactorTerminated =>
      terminated = true
      p.success((excepted, terminated))
  }
  exception.test("Exception thrown in ctor (THIS IS OK)!")
}


class TerminationExceptionReactor(val p: Promise[Boolean]) extends Reactor[Unit] {
  sysEvents onMatch {
    case ReactorDied(t) =>
      p.success(true)
    case ReactorPreempted =>
      main.seal()
    case ReactorTerminated =>
      exception.test("Exception during termination (THIS IS OK)!")
  }
}


class RunningExceptionReactor(val p: Promise[Throwable]) extends Reactor[String] {
  main.events onMatch {
    case "die" => exception.test("Exception thrown (THIS IS OK)!")
  }
  sysEvents onMatch {
    case ReactorDied(t) => p.success(t)
  }
}


object Log {
  def apply(msg: String) = println(s"${Thread.currentThread.getName}: $msg")
}


class RingReactor(
  val index: Int,
  val num: Int,
  val sink: Either[Promise[Boolean], Channel[String]],
  val sched: String
) extends Reactor[String] {

  val next: Channel[String] = {
    if (index == 0) {
      val p = Proto[RingReactor](index + 1, num, Right(main.channel), sched)
        .withScheduler(sched)
      system.spawn(p)
    } else if (index < num) {
      val p = Proto[RingReactor](index + 1, num, sink, sched).withScheduler(sched)
      system.spawn(p)
    } else {
      sink match {
        case Right(first) => first
        case _ => sys.error("unexpected case")
      }
    }
  }

  main.events onMatch {
    case "start" =>
      next ! "ping"
    case "ping" =>
      next ! "ping"
      main.seal()
      if (index == 0) sink match {
        case Left(p) => p.success(true)
        case _ => sys.error("unexpected case")
      }
  }
}


class NamedReactor(val p: Promise[Boolean]) extends Reactor[String] {
  main.events onMatch {
    case "die" =>
      main.seal()
      p.success(true)
  }
}


abstract class BaseJvmReactorSystemCheck(name: String) extends Properties(name) {

  val system = ReactorSystem.default("check-system")

  val scheduler: String

  property("should send itself messages") = forAllNoShrink(choose(1, 1024)) { num =>
    val p = Promise[Boolean]()
    var n = num
    val proto = Reactor[String] { self =>
      self.sysEvents onMatch {
        case ReactorPreempted =>
          if (n > 0) self.main.channel ! "count"
          else {
            if (self.main.seal()) p.success(true)
          }
      }
      self.main.events onMatch {
        case "count" => n -= 1
      }
    }
    system.spawn(proto.withScheduler(scheduler))
    Await.result(p.future, 10.seconds)
  }

}


abstract class JvmReactorSystemCheck(name: String)
extends BaseJvmReactorSystemCheck(name) with ExtendedProperties {

  property("should receive many events") = forAllNoShrink(detChoose(1, 1024)) { num =>
    val p = Promise[Boolean]()
    var n = num
    val proto = Reactor[String] { self =>
      val sub = self.main.events onEvent { v =>
        n -= 1
        if (n <= 0) {
          p.success(true)
          self.main.seal()
        }
      }
    }
    val ch = system.spawn(proto.withScheduler(scheduler))
    for (i <- 0 until n) ch ! "count"
    Await.result(p.future, 10.seconds)
  }

  property("be executed by at most one thread at a time") =
    forAllNoShrink(detChoose(1, 32000)) { n =>
      val count = Promise[Int]()
      val done = Promise[Boolean]()
      val proto = Reactor[String] { self =>
        var threadCount = 0
        var left = n
        self.main.events onMatch {
          case "dec" =>
            if (threadCount != 1) count.success(threadCount)
            left -= 1
            if (left == 0) self.main.seal()
        }
        self.sysEvents onMatch {
          case ReactorScheduled => threadCount += 1
          case ReactorPreempted => threadCount -= 1
          case ReactorTerminated => done.success(true)
        }
      }
      val ch = system.spawn(proto.withScheduler(scheduler))
      for (group <- (0 until n).grouped(n / 4 + 1)) Future {
        for (e <- group) ch ! "dec"
      }
      Await.ready(done.future, 10.seconds)
      assert(!count.future.value.isInstanceOf[Some[_]], count.future.value)
      done.future.value == Some(Success(true))
    }

  property("not process events sent by itself and others after getting sealed") =
    forAllNoShrink(detChoose(1, 16000)) { n =>
      val done = Promise[Boolean]()
      val failed = Promise[Boolean]()
      val proto = Reactor[String] { self =>
        var left = n
        self.main.events onMatch {
          case "dec" =>
            if (left > 0) left -= 1
            else if (left == 0) {
              self.main.seal()
              done.success(true)
            } else {
              failed.success(true)
            }
            self.main.channel ! "dec"
        }
      }
      val ch = system.spawn(proto.withScheduler(scheduler))
      for (group <- (0 until (2 * n)).grouped(n / 4 + 1)) Future {
        for (e <- group) ch ! "dec"
      }
      assert(Await.result(done.future, 10.seconds))
      Thread.sleep(1)
      failed.future.value != Some(Success(true))
    }

  property("receive many events through different sources") =
    forAllNoShrink(choose(1, 1024)) { n =>
      val p = Promise[Boolean]()
      val proto = Reactor[Int] { self =>
        new Reactor.Placeholder {
          val rem = mutable.Set[Int]()
          for (i <- 0 until n) rem += i
          val odd = self.system.channels.open[Int]
          odd.events onEvent { v =>
            rem -= v
            check()
          }
          val even = self.system.channels.open[Int]
          even.events onEvent { v =>
            rem -= v
            check()
          }
          def check() {
            if (rem.size == 0) {
              self.main.seal()
              odd.seal()
              even.seal()
              p.success(true)
            }
          }
          self.main.events onEvent { v =>
            if (v % 2 == 0) even.channel ! v
            else odd.channel ! v
          }
        }
      }
      val ch = system.spawn(proto.withScheduler(scheduler))
      for (i <- 0 until n) ch ! i
      Await.result(p.future, 10.seconds)
    }

  property("be terminated after all its channels are sealed") =
    forAllNoShrink(choose(1, 128)) { n =>
      val p = Promise[Boolean]()
      val proto = Reactor[Int] { self =>
        var c = n
        val connectors = for (i <- 0 until n) yield {
          val conn = self.system.channels.open[Int]
          conn.events onEvent { j =>
            if (i == j) conn.seal()
          }
          conn
        }
        self.main.events onEvent {
          i => connectors(i).channel ! i
        }
        self.main.events.scanPast(n)((count, _) => count - 1) onEvent { i =>
          if (i == 0) self.main.seal()
        }
        self.sysEvents onMatch {
          case ReactorTerminated => p.success(true)
        }
      }
      val ch = system.spawn(proto.withScheduler(scheduler))
      for (i <- 0 until n) {
        Thread.sleep(0)
        ch ! i
      }
      Await.result(p.future, 10.seconds)
    }

  property("should create another reactor and send it messages") =
    forAllNoShrink(choose(1, 512)) { n =>
      val p = Promise[Boolean]()
      val s = scheduler
      val proto = Reactor[Unit] { self =>
        val proto = Reactor[Int] { self =>
          var nextNumber = 0
          val sub = self.main.events onEvent { i =>
            if (nextNumber == i) nextNumber += 1
            if (nextNumber == n) {
              self.main.seal()
              p.success(true)
            }
          }
        }
        val ch = self.system.spawn(proto.withScheduler(s))
        for (i <- 0 until n) ch ! i
        self.main.seal()
      }
      system.spawn(proto.withScheduler(scheduler))
      Await.result(p.future, 10.seconds)
    }

  property("should play ping-pong with another reactor") =
    forAllNoShrink(choose(1, 512)) { num =>
      val p = Promise[Boolean]()
      val s = scheduler
      var n = num
      def pongProto(ping: Channel[String]): Proto[Reactor[String]] = Reactor[String] {
        self =>
        var n = num
        self.main.events onMatch {
          case "pong" =>
            ping ! "ping"
            n -= 1
            if (n == 0) self.main.seal()
        }
      }
      val pingProto = Reactor[String] { self =>
        val pong = self.system.spawn(pongProto(self.main.channel).withScheduler(s))
        val start = self.sysEvents onMatch {
          case ReactorStarted => pong ! "pong"
        }
        val sub = self.main.events onMatch {
          case "ping" =>
            n -= 1
            if (n > 0) pong ! "pong"
            else {
              self.main.seal()
              p.success(true)
            }
        }
      }
      system.spawn(pingProto.withScheduler(scheduler))
      Await.result(p.future, 10.seconds)
    }

  property("a ring of isolates should correctly propagate messages") =
    forAllNoShrink(choose(1, 64)) { n =>
      val p = Promise[Boolean]()
      val proto = Proto[RingReactor](0, n, Left(p), scheduler).withScheduler(scheduler)
      val ch = system.spawn(proto)
      ch ! "start"
      Await.result(p.future, 10.seconds)
    }

  property("should receive all system events") =
    forAllNoShrink(choose(1, 128)) { n =>
      val p = Promise[Boolean]()
      val proto = Reactor[String] { self =>
        val events = mutable.Buffer[SysEvent]()
        self.sysEvents onMatch {
          case ReactorTerminated =>
            val expected = Seq(
              ReactorStarted,
              ReactorScheduled,
              ReactorPreempted)
            p.trySuccess(events == expected)
          case e =>
            events += e
            if (events.size == 3) self.main.seal()
        }
      }
      system.spawn(proto.withScheduler(scheduler))
      Await.result(p.future, 10.seconds)
    }

  property("not process any events after sealing") =
    forAllNoShrink(detChoose(1, 32000)) { n =>
      val total = 32000
      val p = Promise[Boolean]()
      val fail = Promise[Boolean]()
      val max = n
      val proto = Reactor[String] { self =>
        var seen = 0
        var terminated = false
        self.main.events onEvent { s =>
          if (terminated) {
            fail.success(true)
          } else {
            seen += 1
            if (seen >= max) {
              terminated = true
              self.main.seal()
            }
          }
        }
        self.sysEvents onMatch {
          case ReactorTerminated =>
            p.success(true)
        }
      }
      val ch = system.spawn(proto.withScheduler(scheduler))
      for (i <- 0 until total) ch ! "msg"
      assert(Await.result(p.future, 10.seconds))
      Thread.sleep(2)
      fail.future.value != Some(Success(true))
    }

  property("always receive unreact after getting sealed") =
    forAllNoShrink(detChoose(1, 32000)) { n =>
      stackTraced {
        val done = Promise[Boolean]()
        val proto = Reactor[String] { self =>
          var left = n
          self.main.events onEvent {
            case "dec" =>
              if (left > 0) left -= 1
              if (left == 0) self.main.seal()
          }
          self.main.events onDone {
            done.success(true)
          }
        }
        val ch = system.spawn(proto)
        for (x <- 0 until n) ch ! "dec"
        assert(Await.result(done.future, 10.seconds))
        true
      }
    }

  property("receive events in the same order they were sent") =
    forAllNoShrink(detChoose(1, 32000)) { n =>
      stackTraced {
        val done = Promise[Seq[Int]]()
        val proto = Reactor[Int] { self =>
          val seen = mutable.Buffer[Int]()
          self.main.events.onEvent { i =>
            seen += i
            if (i == n - 1) {
              done.success(seen)
              self.main.seal()
            }
          }
        }
        val ch = system.spawn(proto)
        for (x <- 0 until n) ch ! x
        assert(Await.result(done.future, 10.seconds) == (0 until n))
        true
      }
    }

  property("ReactorScheduled before event, ReactorPreempted after event") =
    forAllNoShrink(detChoose(1, 32000)) { n =>
      stackTraced {
        val done = Promise[Boolean]()
        val proto = Reactor[Int] { self =>
          var seqnumber = 0
          var left = n
          self.main.events.onEvent { i =>
            if (seqnumber % 2 == 0) done.success(false)
            left -= 1
            if (left == 0) {
              done.success(true)
              self.main.seal()
            }
          }
          self.sysEvents.onMatch {
            case ReactorScheduled => if (seqnumber % 2 == 0) seqnumber += 1
            case ReactorPreempted => if (seqnumber % 2 == 1) seqnumber += 1
          }
        }
        val ch = system.spawn(proto)
        for (x <- 0 until n) ch ! x
        assert(Await.result(done.future, 10.seconds))
        true
      }
    }

}


object NewThreadReactorSystemCheck
extends JvmReactorSystemCheck("NewThreadSystem") {
  val scheduler = JvmScheduler.Key.newThread
}


object GlobalExecutionContextReactorSystemCheck
extends JvmReactorSystemCheck("ECSystem") {
  val scheduler = JvmScheduler.Key.globalExecutionContext
}


object DefaultJvmSchedulerReactorSystemCheck
extends JvmReactorSystemCheck("DefaultJvmSchedulerSystem") {
  val scheduler = JvmScheduler.Key.default
}


object PiggybackReactorSystemCheck
extends BaseJvmReactorSystemCheck("PiggybackSystem") {
  val scheduler = JvmScheduler.Key.piggyback
}


class JvmReactorSystemTest extends AnyFunSuite with Matchers {
  test("reactor should terminate on ctor exception") {
    val scheduler = new JvmScheduler.Dedicated.NewThread(true)
    val bundle = ReactorSystem.Bundle.default(scheduler)
    val system = ReactorSystem.default("test", bundle)
    try {
      val p = Promise[(Boolean, Boolean)]()
      system.spawn(Proto[CtorExceptionReactor](p))
      assert(Await.result(p.future, 10.seconds) == (true, true))
    } finally system.shutdown()
  }

  test("reactor does not raise ReactorDied events after ReactorTerminated") {
    val scheduler = new JvmScheduler.Dedicated.NewThread(true)
    val bundle = ReactorSystem.Bundle.default(scheduler)
    val system = ReactorSystem.default("test", bundle)
    try {
      val p = Promise[Boolean]()
      system.spawn(Proto[TerminationExceptionReactor](p))
      Thread.sleep(1000)
      assert(p.future.value == None)
    } finally system.shutdown()
  }

  test("reactor should terminate on exceptions while running") {
    val scheduler = new JvmScheduler.Dedicated.NewThread(true)
    val bundle = ReactorSystem.Bundle.default(scheduler)
    val system = ReactorSystem.default("test", bundle)
    try {
      val p = Promise[Throwable]()
      val ch = system.spawn(Proto[RunningExceptionReactor](p))
      ch ! "die"
      val expected = "Exception thrown (THIS IS OK)!"
      assert(Await.result(p.future, 10.seconds).getMessage == expected)
    } finally system.shutdown()
  }

  test("piggyback scheduler should throw an exception if called from a reactor") {
    val system = ReactorSystem.default("test")
    try {
      val p = Promise[Boolean]()
      system.spawn(Proto[PiggyReactor](p))
      assert(Await.result(p.future, 10.seconds))
    } finally system.shutdown()
  }
}
