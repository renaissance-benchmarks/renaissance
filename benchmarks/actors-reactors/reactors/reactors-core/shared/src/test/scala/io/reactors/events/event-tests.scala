package io.reactors
package events



import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Gen.choose
import org.scalatest._
import org.scalatest.exceptions.TestFailedException
import io.reactors.common.Conc
import io.reactors.common.Ref
import io.reactors.test._
import scala.collection._
import scala.util._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers



class EventsSpec extends AnyFunSuite {

  class TestEmitter[T] extends Events.Emitter[T] {
    var unsubscriptionCount = 0
    override def onReaction(obs: Observer[T]) = new Subscription.Composite(
      super.onReaction(obs),
      new Subscription {
        def unsubscribe() = unsubscriptionCount += 1
      }
    )
  }

  test("closed emitter immediately unreacts") {
    val emitter = new Events.Emitter[Int]
    emitter.unreact()

    var done = false
    emitter.onDone({ done = true })
    assert(done)
  }

  test("onReaction") {
    var event: String = null
    var exception: Throwable = null
    var done = false
    val emitter = new Events.Emitter[String]
    val sub = emitter.onReaction(new Observer[String] {
      def react(x: String, hint: Any) = event = x
      def except(t: Throwable) = exception = t
      def unreact() = done = true
    })

    emitter.react("ok")
    assert(event == "ok")
    assert(exception == null)
    assert(!done)

    val e = new RuntimeException("not ok")
    emitter.except(e)
    assert(event == "ok")
    assert(exception == e)
    assert(!done)

    emitter.unreact()
    assert(event == "ok")
    assert(exception == e)
    assert(done)

    emitter.react(null)
    emitter.except(null)
    assert(event == "ok")
    assert(exception == e)
    assert(done)
  }

  test("onReaction with early unsubscribe") {
    var event: String = null
    var exception: Throwable = null
    var done = false
    val emitter = new Events.Emitter[String]
    val sub = emitter.onReaction(new Observer[String] {
      def react(x: String, hint: Any) = event = x
      def except(t: Throwable) = exception = t
      def unreact() = done = true
    })

    emitter.react("ok")
    assert(event == "ok")
    assert(exception == null)
    assert(!done)

    sub.unsubscribe()

    emitter.react("hmph")
    assert(event == "ok")
    assert(exception == null)
    assert(!done)
  }

  test("onEventOrDone") {
    var event: String = null
    var done = false
    val emitter = new Events.Emitter[String]
    val sub = emitter.onEventOrDone {
      event = _
    } {
      done = true
    }

    emitter.react("ok")
    assert(event == "ok")
    assert(!done)

    emitter.unreact()
    assert(event == "ok")
    assert(done)
  }

  test("onEvent") {
    var event: String = null
    val emitter = new Events.Emitter[String]
    val sub = emitter.onEvent(event = _)
  
    emitter.react("ok")
    assert(event == "ok")
    
    sub.unsubscribe()
    
    emitter.react("lost")
    assert(event == "ok")
  }

  test("onMatch") {
    var event: String = null
    val emitter = new Events.Emitter[String]
    val sub = emitter onMatch {
      case x if x.length < 5 => event = x
    }

    emitter.react("ok")
    assert(event == "ok")

    emitter.react("long'n'lost")
    assert(event == "ok")

    sub.unsubscribe()

    emitter.react("boom")
    assert(event == "ok")
  }

  test("on") {
    var count = 0
    val emitter = new Events.Emitter[String]
    val sub = emitter.on(count += 1)

    emitter.react("bam")
    assert(count == 1)

    emitter.react("babaluj")
    assert(count == 2)

    sub.unsubscribe()
    
    emitter.react("foo")
    assert(count == 2)
  }

  test("onDone") {
    var done = false
    val emitter = new Events.Emitter[String]
    val sub = emitter.onDone({ done = true })

    emitter.react("bam")
    assert(!done)

    emitter.unreact()
    assert(done)
  }

  test("onDone unsubscribe") {
    var done = false
    val emitter = new Events.Emitter[String]
    val sub = emitter.onDone({ done = true })

    emitter.react("ok")
    assert(!done)

    sub.unsubscribe()

    emitter.unreact()
    assert(!done)
  }

  test("onExcept") {
    var found = false
    val emitter = new Events.Emitter[String]
    val sub = emitter onExcept {
      case e: IllegalArgumentException => found = true
      case _ => // ignore
    }

    emitter.except(new RuntimeException)
    assert(!found)

    emitter.except(new IllegalArgumentException)
    assert(found)
  }

  test("recover") {
    val buffer = mutable.Buffer[String]()
    val emitter = new Events.Emitter[String]
    val sub = emitter recover {
      case e: IllegalArgumentException => "kaboom"
    } onEvent(buffer += _)

    emitter.react("ok")
    assert(buffer == Seq("ok"))

    emitter.except(new IllegalArgumentException)
    assert(buffer == Seq("ok", "kaboom"))

    intercept[UnhandledException] {
      emitter.except(new RuntimeException)
    }
    
    sub.unsubscribe()
    
    emitter.except(new RuntimeException)
    assert(buffer == Seq("ok", "kaboom"))
  }

  test("lift try") {
    val buffer = mutable.Buffer[Try[String]]()
    val emitter = new Events.Emitter[String]()
    emitter.liftTry.onEvent(buffer += _)
    emitter.react("ok")
    assert(buffer == Seq(Success("ok")))
    emitter.except(new Exception("not ok"))
    val failure = Failure(new Exception("not ok"))
    assert(buffer(1).asInstanceOf[Failure[String]].exception.getMessage == "not ok")
    emitter.react("ok again")
    assert(buffer(2) == Success("ok again"))
  }

  test("ignoreExceptions") {
    var seen = false
    val emitter = new Events.Emitter[String]
    val sub = emitter.ignoreExceptions.on({ seen = true })

    emitter.except(new RuntimeException)
    assert(!seen)
  }

  test("scanPast") {
    val buffer = mutable.Buffer[String]()
    val emitter = new Events.Emitter[String]
    val longest = emitter.scanPast("") { (prev, x) =>
      if (prev.length < x.length) x else prev
    }
    val sub = longest.onEvent(buffer += _)

    emitter.react("one")
    emitter.react("two")
    emitter.react("three")
    emitter.react("five")
    emitter.react("seven")
    emitter.react("eleven")

    assert(buffer == Seq("one", "one", "three", "three", "three", "eleven"))
  }

  test("scanPast with Int") {
    val buffer = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[Int]
    val sum = emitter.scanPast(0)(_ + _)
    val sub = sum.onEvent(buffer += _)

    emitter.react(0)
    emitter.react(1)
    emitter.react(2)
    emitter.react(3)
    emitter.react(4)
    emitter.react(5)

    assert(buffer == Seq(0, 1, 3, 6, 10, 15))
  }

  test("reducePast") {
    val buffer = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[Int]
    val sum = emitter.reducePast(0)(_ + _)
    val sub = sum.onEvent(buffer += _)

    emitter.react(0)
    emitter.react(1)
    emitter.react(2)
    emitter.react(3)
    emitter.react(4)
    emitter.react(5)
    assert(buffer == Seq())
    emitter.unreact()
    assert(buffer == Seq(15))
  }

  test("incremental") {
    val seen = mutable.Buffer[Int]()
    var unsubscribed = false
    val emitter = new Events.Emitter[Int]
    val tick = new Events.Emitter[Unit]
    val samples = tick.incremental[Int] {
      val state = emitter.toSignal(0)
      (state.andThen({ unsubscribed = true }), obs => obs.react(state(), null))
    }
    samples.onEvent(seen += _)
    assert(seen == Seq())
    tick.react(())
    assert(seen == Seq(0))
    emitter.react(11)
    emitter.react(19)
    assert(seen == Seq(0))
    tick.react(())
    assert(seen == Seq(0, 19))
    assert(!unsubscribed)
    tick.unreact()
    assert(seen == Seq(0, 19))
    assert(unsubscribed)
  }

  test("toEmpty") {
    val emitter = new Events.Emitter[Int]
    val signal = emitter.toEmpty

    intercept[NoSuchElementException] {
      signal()
    }

    emitter.react(7)
    assert(signal() == 7)

    signal.unsubscribe()

    emitter.react(11)
    assert(signal() == 7)
  }

  test("toSignal") {
    val emitter = new Events.Emitter[Int]
    val signal = emitter.toSignal(1)

    assert(signal() == 1)

    emitter.react(7)
    assert(signal() == 7)

    signal.unsubscribe()

    emitter.react(11)
    assert(signal() == 7)
  }

  test("toSignal unreacts observers when done") {
    val emitter = new TestEmitter[Int]
    val signal = emitter.toSignal(7)
    emitter.unreact()

    var done = false
    signal.onDone({ done = true })
    assert(done)
    assert(!emitter.hasSubscriptions)
  }

  test("toCold") {
    val emitter = new Events.Emitter[Int]
    val signal = emitter.toCold(1)

    assert(signal() == 1)

    emitter.react(7)
    assert(signal() == 1)

    var last = 0
    val sub0 = signal.onEvent(last = _)
    emitter.react(11)
    assert(signal() == 11)
    assert(last == 11)

    sub0.unsubscribe()
    emitter.react(17)
    assert(signal() == 11)
    assert(last == 11)

    val sub1 = signal.onEvent(last = _)
    emitter.react(19)
    assert(signal() == 19)
    assert(last == 19)
  }

  test("toCold unsubscribes with zero subscribers") {
    val emitter = new TestEmitter[Int]
    val signal = emitter.toCold(7)

    var last = 0
    val sub0 = signal.onEvent(last = _)

    emitter.react(11)
    assert(last == 11)

    sub0.unsubscribe()
    assert(emitter.unsubscriptionCount == 1)

    val sub1 = signal.onEvent(last = _)
    val sub2 = signal.onEvent(last = _)

    sub1.unsubscribe()
    assert(emitter.unsubscriptionCount == 1)
    sub2.unsubscribe()
    assert(emitter.unsubscriptionCount == 2)
  }

  test("toCold unreacts observers when done") {
    val emitter = new TestEmitter[Int]
    val signal = emitter.toCold(7)
    assert(!emitter.hasSubscriptions)
    signal.on({})
    assert(emitter.hasSubscriptions)
    emitter.unreact()
    assert(!emitter.hasSubscriptions)

    var done = false
    signal.onDone({ done = true })
    assert(done)
    assert(!emitter.hasSubscriptions)
  }

  test("toCold used with zip removes subscriptions") {
    val e0 = new TestEmitter[Int]
    val e1 = new TestEmitter[Int]
    var done = false
    (e0.toCold(3) zip e1.toCold(7))(_ + _).onDone({ done = true })

    e0.react(1)
    e1.react(2)
    e0.unreact()
    assert(!done)
    e1.unreact()
    assert(done)
    assert(!e0.hasSubscriptions)
    assert(!e1.hasSubscriptions)
  }

  test("count") {
    val buffer = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[String]
    val sub = emitter.count.onEvent(buffer += _)

    emitter.react("a")
    emitter.react("b")
    emitter.react("c")

    assert(buffer == Seq(1, 2, 3))
  }

  test("mutate") {
    var len = 0
    val log = new Events.Mutable(mutable.Buffer[String]())
    val emitter = new Events.Emitter[String]
    val s1 = emitter.mutate(log) { buffer => s =>
      buffer += s
    }
    val s2 = log.onEvent(x => len = x.length)

    emitter.react("one")
    assert(len == 1)

    emitter.react("two")
    assert(len == 2)

    assert(log.content == Seq("one", "two"))
  }

  test("mutate2") {
    var len = 0
    val log1 = new Events.Mutable(mutable.Buffer[String]())
    val log2 = new Events.Mutable(mutable.Buffer[Int]())
    val emitter = new Events.Emitter[String]
    emitter.mutate(log1, log2) { (b1, b2) => s =>
      b1 += s
      b2 += len
    }
    log1.onEvent(b => len = b.length)

    emitter.react("ok")
    assert(log1.content == Seq("ok"))
    assert(log2.content == Seq(0))
  }

  test("mutate3") {
    var len = 0
    var last = ""
    val log1 = new Events.Mutable(mutable.Buffer[String]())
    val log2 = new Events.Mutable(mutable.Buffer[String]())
    val log3 = new Events.Mutable(mutable.Buffer[Int]())
    val emitter = new Events.Emitter[String]
    emitter.mutate(log1, log2, log3) { (b1, b2, b3) => s =>
      b1 += s
      b2 += last
      b3 += len
    }
    log1.onEvent(b => last = b.last)
    log2.onEvent(b => len = b.length)

    emitter.react("ok")
    assert(log1.content == Seq("ok"))
    assert(log2.content == Seq(""))
    assert(log3.content == Seq(0))
  }

  test("after") {
    var seen = false
    val emitter = new Events.Emitter[Int]
    val start = new Events.Emitter[Unit]
    val after = emitter.after(start)
    after.on({ seen = true })

    emitter.react(7)
    assert(!seen)

    start.react(())
    emitter.react(11)
    assert(seen)
  }

  test("after with Int") {
    var seen = false
    val emitter = new Events.Emitter[Int]
    val start = new Events.Emitter[Int]
    val after = emitter.after(start)
    after.on({ seen = true })

    emitter.react(7)
    assert(!seen)

    start.react(11)
    emitter.react(17)
    assert(seen)
  }

  test("after unsubscribes") {
    val emitter = new Events.Emitter[Int]
    val start = new TestEmitter[Int]
    emitter.after(start).on({})

    assert(start.unsubscriptionCount == 0)
    start.react(1)
    assert(start.unsubscriptionCount == 1)
  }

  test("until") {
    var sum = 0
    val emitter = new Events.Emitter[Int]
    val end = new Events.Emitter[Int]
    val until = emitter.until(end)
    until.onEvent(sum += _)

    emitter.react(7)
    assert(sum == 7)

    emitter.react(19)
    assert(sum == 26)

    end.react(11)
    emitter.react(17)
    assert(sum == 26)
  }

  test("defer") {
    var done = false
    var seen = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[Int]
    val go = new IVar[Boolean]
    val deferred = emitter.defer(go)
    deferred.onEventOrDone(seen += _)({ done = true })

    emitter.react(7)
    assert(!done)
    assert(seen == Seq())
    emitter.react(11)
    assert(seen == Seq())
    go.react(true)
    assert(seen == Seq(7, 11))
    emitter.react(17)
    assert(seen == Seq(7, 11, 17))
    assert(!done)
    emitter.unreact()
    assert(seen == Seq(7, 11, 17))
    assert(done)
  }

  test("defer early unreact") {
    var done = false
    var seen = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[Int]
    val go = new IVar[Boolean]
    val deferred = emitter.defer(go)
    deferred.onEventOrDone(seen += _)({ done = true })

    emitter.react(7)
    assert(!done)
    assert(seen == Seq())
    emitter.react(11)
    assert(seen == Seq())
    emitter.unreact()
    assert(seen == Seq())
    assert(!done)
    go.react(true)
    assert(seen == Seq(7, 11))
    assert(done)
  }

  test("until unsubscribes") {
    val emitter = new TestEmitter[Int]
    val end = new TestEmitter[Int]
    emitter.until(end).on({})

    assert(emitter.unsubscriptionCount == 0)
    assert(end.unsubscriptionCount == 0)
    end.react(1)
    assert(emitter.unsubscriptionCount == 1)
    assert(end.unsubscriptionCount == 1)
  }

  test("changed") {
    val emitter = new Events.Emitter[Int]
    val seen = mutable.Buffer[Int]()
    var done = false
    emitter.changed(0).onEventOrDone(seen += _)({ done = true })

    emitter.react(0)
    assert(seen == Nil)
    emitter.react(1)
    assert(seen == Seq(1))
    emitter.react(5)
    assert(seen == Seq(1, 5))
    emitter.react(5)
    assert(seen == Seq(1, 5))
    emitter.react(7)
    assert(seen == Seq(1, 5, 7))
    assert(!done)
    emitter.unreact()
    assert(done)
  }

  test("once") {
    var count = 0
    var done = 0
    val emitter = new Events.Emitter[Int]
    val once = emitter.once
    once.on(count += 1)
    once.onDone(done += 1)

    emitter.react(7)
    assert(count == 1)
    assert(done == 1)

    emitter.react(11)
    assert(count == 1)
    assert(done == 1)
  }

  test("once with early unreact") {
    var seen = false
    val emitter = new Events.Emitter[String]
    val once = emitter.once
    once.on({ seen = true })

    emitter.unreact()
    assert(!seen)

    emitter.react("kaboom")
    assert(!seen)
  }

  test("once unsubscribes") {
    val emitter = new TestEmitter[Int]
    emitter.once.on({})

    assert(emitter.unsubscriptionCount == 0)
    emitter.react(1)
    assert(emitter.unsubscriptionCount == 1)
  }

  test("last") {
    var last = -1
    val emitter = new Events.Emitter[Int]
    emitter.last.onEvent(x => last = x)

    emitter.react(3)
    assert(last == -1)
    emitter.react(5)
    assert(last == -1)
    emitter.react(7)
    assert(last == -1)
    emitter.react(11)
    assert(last == -1)
    emitter.unreact()
    assert(last == 11)
  }

  test("last early done") {
    var last = -1
    var done = false
    val emitter = new Events.Emitter[Int]
    emitter.last.onEventOrDone(x => last = x)({ done = true })

    emitter.unreact()
    assert(last == -1)
    assert(done)
  }

  test("single") {
    var elem = -1
    var done = false
    Events.single(7).onEventOrDone(elem = _)({ done = true })
    assert(elem == 7)
    assert(done)
  }

  test("filter") {
    val buffer = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[Int]
    emitter.filter(_ % 2 == 0).onEvent(buffer += _)

    emitter.react(1)
    assert(buffer == Seq())

    emitter.react(4)
    assert(buffer == Seq(4))

    emitter.react(9)
    assert(buffer == Seq(4))

    emitter.react(10)
    assert(buffer == Seq(4, 10))

    emitter.unreact()
    emitter.react(16)
    assert(buffer == Seq(4, 10))
  }

  test("collect") {
    val buffer = mutable.Buffer[String]()
    val emitter = new Events.Emitter[String]
    val collect = emitter.collect {
      case "ok" => "ok!"
    }
    collect.onEvent(buffer += _)

    emitter.react("not ok")
    assert(buffer == Seq())

    emitter.react("ok")
    assert(buffer == Seq("ok!"))
  }

  test("map") {
    val buffer = mutable.Buffer[String]()
    val emitter = new Events.Emitter[Int]
    emitter.map(_.toString).onEvent(buffer += _)

    emitter.react(7)
    assert(buffer == Seq("7"))

    emitter.react(11)
    assert(buffer == Seq("7", "11"))
  }

  test("sample") {
    val cell = RCell(4)
    val emitter = new Events.Emitter[Unit]
    val sampled = emitter.sample(cell())
    val seen = mutable.Buffer[Int]()
    sampled.onEvent(seen += _)
    cell := 5
    emitter.react(())
    assert(seen == Seq(5))
    cell := 6
    cell := 7
    emitter.react(())
    assert(seen == Seq(5, 7))
  }

  test("group by") {
    val es = new Events.Emitter[Int]
    val gs = es.groupBy(_ % 3)
    val seen = mutable.Map[Int, mutable.Set[Int]]()
    val done = mutable.Set[Int]()
    val sub = gs onMatch {
      case (k, events) =>
        seen(k) = mutable.Set[Int]()
        events.onEventOrDone(seen(k) += _)(done += k)
    }
    es.react(2)
    assert(seen(2) == Set(2))
    assert(done.isEmpty)
    es.react(1)
    assert(seen(1) == Set(1))
    assert(done.isEmpty)
    es.react(7)
    assert(seen(1) == Set(1, 7))
    assert(done.isEmpty)
    es.unreact()
    assert(done == Set(1, 2))
  }

  test("batch") {
    val es = new Events.Emitter[Int]
    val bs = es.batch(3)
    val seen = mutable.Buffer[Seq[Int]]()
    bs.onEvent(seen += _)
    for (i <- 0 until 7) es.react(i)
    es.unreact()
    assert(seen == Seq(Seq(0, 1, 2), Seq(3, 4, 5), Seq(6)))
  }

  test("takeWhile") {
    val buffer = mutable.Buffer[String]()
    val emitter = new Events.Emitter[String]
    emitter.takeWhile(_.length < 5).onEvent(buffer += _)

    emitter.react("one")
    emitter.react("four")
    emitter.react("seven")
    emitter.react("ten")

    assert(buffer == Seq("one", "four"))
  }

  test("takeWhile unsubscribes early") {
    val emitter = new TestEmitter[Int]
    emitter.takeWhile(_ < 3).on({})

    emitter.react(1)
    assert(emitter.unsubscriptionCount == 0)
    emitter.react(2)
    assert(emitter.unsubscriptionCount == 0)
    emitter.react(3)
    assert(emitter.unsubscriptionCount == 1)
  }

  test("dropAfter") {
    val buffer = mutable.Buffer[String]()
    val emitter = new Events.Emitter[String]
    emitter.takeWhile(_.length < 5).onEvent(buffer += _)

    emitter.react("one")
    emitter.react("four")
    emitter.react("seven")
    emitter.react("ten")

    assert(buffer == Seq("one", "four"))
  }

  test("dropWhile") {
    val buffer = mutable.Buffer[String]()
    val emitter = new Events.Emitter[String]
    emitter.dropWhile(_.length < 5).onEvent(buffer += _)

    emitter.react("one")
    emitter.react("two")
    emitter.react("three")
    emitter.react("nil")

    assert(buffer == Seq("three", "nil"))
  }

  test("take") {
    val buffer = mutable.Buffer[String]()
    val emitter = new Events.Emitter[String]
    var done = false
    emitter.take(2).onEvent(buffer += _)
    emitter.take(2).onDone({ done = true })

    emitter.react("one")
    assert(!done)
    emitter.react("two")
    assert(done)
    emitter.react("three")
    assert(buffer == Seq("one", "two"))
  }

  test("mux") {
    var sum = 0
    val emitter = new Events.Emitter[Events[Int]]
    emitter.mux.onEvent(sum += _)

    val e1 = new Events.Emitter[Int]
    val e2 = new Events.Emitter[Int]
    e1.react(3)
    e2.react(5)
    assert(sum == 0)

    emitter.react(e1)
    e1.react(7)
    e2.react(11)
    assert(sum == 7)

    emitter.react(e2)
    e1.react(17)
    e2.react(19)
    assert(sum == 26)

    e2.unreact()
    emitter.react(e1)
    e1.react(23)
    assert(sum == 49)

    emitter.unreact()
    e1.react(29)
    assert(sum == 78)
  }

  test("mux another subscription") {
    var want1 = 0
    var want1Too = 0

    val have0 = new Events.Emitter[Int]
    val factory = new Events.Emitter[Events[Int]]
    val mux = factory.mux.toSignal(0)
    val map = mux.map(x => x + 1)

    map.onEvent(x => want1 = x)
    factory.react(have0)
    map.onEvent(x => want1Too = x)
    have0.react(0)

    assert(want1 == 1)
    assert(want1Too == 1)
  }

  test("unreacted") {
    var count = 0
    val emitter = new Events.Emitter[Int]
    emitter.done.on(count += 1)

    emitter.react(5)
    assert(count == 0)
    emitter.unreact()
    assert(count == 1)
  }

  test("unreacted unsubscribes early") {
    val emitter = new TestEmitter[Int]
    emitter.done.on({})
    emitter.unreact()
    assert(emitter.unsubscriptionCount == 1)
  }

  test("union") {
    var done = false
    val buffer = mutable.Buffer[String]()
    val e0 = new Events.Emitter[String]
    val e1 = new Events.Emitter[String]
    val union = e0 union e1
    union.onEvent(buffer += _)
    union.onDone({ done = true })

    e0.react("bam")
    assert(buffer == Seq("bam"))
    e1.react("boom")
    assert(buffer == Seq("bam", "boom"))
    e0.react("dam")
    assert(buffer == Seq("bam", "boom", "dam"))
    e0.unreact()
    e1.react("van dam")
    assert(buffer == Seq("bam", "boom", "dam", "van dam"))
    assert(!done)
    e1.unreact()
    assert(done)
  }

  test("concat") {
    var done = false
    val buffer = mutable.Buffer[Int]()
    val e0 = new Events.Emitter[Int]
    val e1 = new Events.Emitter[Int]
    val concat = e0 concat e1
    concat.onEvent(buffer += _)
    concat.onDone({ done = true })

    e0.react(3)
    assert(buffer == Seq(3))
    e1.react(7)
    assert(buffer == Seq(3))
    e0.react(5)
    assert(buffer == Seq(3, 5))
    e0.unreact()
    assert(buffer == Seq(3, 5, 7))
    e1.react(11)
    assert(buffer == Seq(3, 5, 7, 11))
    assert(!done)
    e1.unreact()
    assert(done)
  }

  test("sync") {
    var done = false
    val buffer = mutable.Buffer[Int]()
    val e0 = new Events.Emitter[Int]
    val e1 = new Events.Emitter[Int]
    val sync = (e0 sync e1)(_ + _)
    sync.onEvent(buffer += _)
    sync.onDone({ done = true })

    e0.react(3)
    assert(buffer == Seq())
    e1.react(5)
    assert(buffer == Seq(8))
    e1.react(7)
    e1.react(11)
    assert(buffer == Seq(8))
    e0.react(19)
    assert(buffer == Seq(8, 26))
    assert(!done)
    e1.unreact()
    assert(buffer == Seq(8, 26))
    assert(done)
  }

  test("sync many") {
    var done = false
    val buffer = mutable.Buffer[Seq[Int]]()
    val e0 = new Events.Emitter[Int]
    val e1 = new Events.Emitter[Int]
    val e2 = new Events.Emitter[Int]
    val sync = Events.sync(e0, e1, e2)
    sync.onEvent(buffer += _)
    sync.onDone({ done = true })

    e0.react(3)
    assert(!done)
    assert(buffer == Seq())
    e0.react(5)
    assert(!done)
    assert(buffer == Seq())
    e1.react(13)
    assert(!done)
    assert(buffer == Seq())
    e2.react(23)
    assert(!done)
    assert(buffer == Seq(Seq(3, 13, 23)))
    e2.react(25)
    assert(!done)
    assert(buffer == Seq(Seq(3, 13, 23)))
    e1.react(15)
    assert(!done)
    assert(buffer == Seq(Seq(3, 13, 23), Seq(5, 15, 25)))
    e0.react(7)
    assert(!done)
    assert(buffer == Seq(Seq(3, 13, 23), Seq(5, 15, 25)))
    e1.unreact()
    assert(done)
    assert(buffer == Seq(Seq(3, 13, 23), Seq(5, 15, 25)))
  }

  test("reverse") {
    var done = false
    val seen = mutable.Buffer[Int]()
    val e = new Events.Emitter[Int]
    val reversed = e.reverse
    reversed.onEvent(seen += _)
    reversed.onDone({ done = true })

    e.react(11)
    assert(seen == Seq())
    assert(!done)
    e.react(17)
    assert(seen == Seq())
    assert(!done)
    e.react(19)
    assert(seen == Seq())
    assert(!done)
    e.unreact()
    assert(seen == Seq(19, 17, 11))
    assert(done)
  }

  test("postfix union") {
    var done = false
    val buffer = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[Events.Emitter[Int]]
    val e0 = new Events.Emitter[Int]
    val es = for (i <- 0 until 5) yield new Events.Emitter[Int]
    val union = emitter.union
    union.onEvent(buffer += _)
    union.onDone({ done = true })

    emitter.react(e0)
    assert(!done)
    for (e <- e0 +: es) e.react(7)
    assert(buffer == Seq(7))
    for (e <- es) emitter.react(e)
    for (e <- es) e.react(11)
    assert(buffer == Seq(7, 11, 11, 11, 11 ,11))
    assert(!done)
    e0.unreact()
    assert(!done)
    for (e <- es) e.react(17)
    assert(buffer == Seq(7, 11, 11, 11, 11 ,11, 17, 17, 17, 17, 17))
    emitter.unreact()
    assert(!done)
    for (e <- es) e.unreact()
    assert(done)
  }

  test("postfix concat") {
    var done = false
    val buffer = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[Events.Emitter[Int]]
    val e0 = new Events.Emitter[Int]
    val es = for (i <- 0 until 5) yield new Events.Emitter[Int]
    val e6 = new Events.Emitter[Int]
    val concat = emitter.concat
    concat.onEvent(buffer += _)
    concat.onDone({ done = true })

    emitter.react(e0)
    assert(!done)
    for (e <- e0 +: es) e.react(7)
    assert(buffer == Seq(7))
    for (e <- es) emitter.react(e)
    emitter.react(e6)
    for (e <- es) e.react(11)
    assert(buffer == Seq(7))
    e0.react(11)
    assert(buffer == Seq(7, 11))
    e6.react(17)
    assert(buffer == Seq(7, 11))
    assert(!done)
    e0.unreact()
    assert(!done)
    assert(buffer == Seq(7, 11, 11))
    for (e <- es) e.react(19)
    es.head.unreact()
    assert(buffer == Seq(7, 11, 11, 19, 11, 19))
    for (e <- es) e.unreact()
    assert(buffer == Seq(7, 11, 11, 19, 11, 19, 11, 19, 11, 19, 11, 19, 17))
    emitter.unreact()
    assert(!done)
    e6.react(23)
    assert(buffer == Seq(7, 11, 11, 19, 11, 19, 11, 19, 11, 19, 11, 19, 17, 23))
    e6.unreact()
    assert(done)
  }

  test("postfix first") {
    var done = false
    val emitter = new Events.Emitter[Events[Int]]
    val e0 = new Events.Emitter[Int]
    val e1 = new Events.Emitter[Int]
    val e2 = new Events.Emitter[Int]

    val b0 = mutable.Buffer[Int]()
    val f0 = emitter.first
    f0.onEvent(b0 += _)
    emitter.react(e1)
    emitter.react(e2)
    emitter.react(e0)
    assert(b0 == Seq())
    e1.react(7)
    assert(b0 == Seq(7))
    e2.react(11)
    assert(b0 == Seq(7))
    e0.react(17)
    e1.react(19)
    assert(b0 == Seq(7, 19))

    val b1 = mutable.Buffer[Int]()
    val f1 = emitter.first
    var done1 = false
    f1.onEventOrDone(b1 += _)({ done1 = true })
    emitter.react(e0)
    e0.react(111)
    assert(b1 == Seq(111))
    emitter.react(e1)
    emitter.react(e2)
    e2.react(123)
    e1.react(191)
    assert(b1 == Seq(111))
    e0.react(145)
    assert(b1 == Seq(111, 145))
    e2.unreact()
    e0.react(157)
    assert(b1 == Seq(111, 145, 157))
    e1.react(117)
    e1.unreact()
    e0.react(231)
    assert(b1 == Seq(111, 145, 157, 231))
    assert(!done1)
    e0.unreact()
    assert(done1)
    e0.react(299)
    assert(b1 == Seq(111, 145, 157, 231))

    val e3 = new Events.Emitter[Int]
    val e4 = new Events.Emitter[Int]
    val e5 = new Events.Emitter[Int]
    val b2 = mutable.Buffer[Int]()
    val f2 = emitter.first
    var done2 = false
    f2.onEventOrDone(b2 += _)({ done2 = true })
    emitter.react(e3)
    emitter.react(e4)
    e3.unreact()
    assert(!done2)
    assert(b2 == Seq())
    e4.unreact()
    assert(!done2)
    assert(b2 == Seq())
    emitter.react(e5)
    e5.react(271)
    assert(!done2)
    e5.unreact()
    assert(b2 == Seq(271))
    assert(done2)

    val e6 = new Events.Emitter[Int]
    val e7 = new Events.Emitter[Int]
    val e8 = new Events.Emitter[Int]
    val b3 = mutable.Buffer[Int]()
    val f3 = emitter.first
    var done3 = false
    f3.onEventOrDone(b3 += _)({ done3 = true })
    emitter.react(e6)
    emitter.react(e7)
    emitter.react(e8)
    emitter.unreact()
    e6.react(7)
    assert(!done3)
    assert(b3 == Seq(7))
    e7.react(11)
    emitter.unreact()
    e8.react(17)
    e6.react(23)
    assert(!done3)
    assert(b3 == Seq(7, 23))
    e6.unreact()
    assert(done3)

    val earlyDoneEmitter = new Events.Emitter[Events[Int]]
    val e9 = new Events.Emitter[Int]
    val e10 = new Events.Emitter[Int]
    val b4 = mutable.Buffer[Int]()
    val f4 = earlyDoneEmitter.first
    var done4 = false
    f4.onEventOrDone(b4 += _)({ done4 = true })
    earlyDoneEmitter.react(e9)
    earlyDoneEmitter.react(e10)
    earlyDoneEmitter.unreact()
    assert(!done4)
    e9.unreact()
    assert(!done4)
    e10.unreact()
    assert(done4)
  }

  test("postfix first with early subscription") {
    val e = new Events.Emitter[Int]
    val ivar = IVar(e)
    val f = ivar.first
    val b = mutable.Buffer[Int]()
    var done = false
    f.onEventOrDone(b += _)({ done = true })
    e.react(7)
    assert(b == Seq(7))
    assert(!done)
    e.unreact()
    assert(b == Seq(7))
    assert(done)

    val nested = IVar(11)
    val top = IVar(nested)
    val first = top.first
    val buffer = mutable.Buffer[Int]()
    var completed = false
    first.onEventOrDone(buffer += _)({ completed = true })
    assert(buffer == Seq(11))
    assert(completed)
  }

  test("ivar") {
    var result = 0
    var done = 0
    val emitter = new TestEmitter[Int]
    val ivar = emitter.toIVar
    ivar.onEvent(result += _)
    ivar.onDone(done += 11)

    assert(emitter.hasSubscriptions)
    emitter.react(7)
    assert(result == 7)
    assert(done == 11)
    assert(ivar() == 7)
    assert(ivar.isAssigned)
    assert(ivar.isCompleted)
    assert(!ivar.isFailed)
    assert(!ivar.isUnassigned)
    assert(!emitter.hasSubscriptions)

    emitter.react(17)
    assert(result == 7)
    assert(done == 11)
    assert(ivar() == 7)
    assert(ivar.isAssigned)
    assert(ivar.isCompleted)
    assert(!ivar.isFailed)
    assert(!ivar.isUnassigned)

    emitter.unreact()
    assert(!emitter.hasSubscriptions)
    var last = 0
    var terminated = false
    ivar.onEventOrDone({ last = _ })({ terminated = true })
    assert(last == 7)
    assert(terminated)
    assert(!emitter.hasSubscriptions)
  }

  test("ivar with exception") {
    var result = 0
    var done = 0
    var e: Throwable = null
    val emitter = new Events.Emitter[Int]
    val ivar = emitter.toIVar
    ivar.onReaction(new Observer[Int] {
      def react(x: Int, hint: Any) = result += x
      def except(t: Throwable) = e = t
      def unreact() = done = 11
    })

    emitter.except(new IllegalArgumentException)
    assert(done == 11)
    assert(ivar.failure.isInstanceOf[IllegalArgumentException])
    assert(!ivar.isAssigned)
    assert(ivar.isCompleted)
    assert(ivar.isFailed)
    assert(!ivar.isUnassigned)

    emitter.react(17)
    assert(done == 11)
    assert(ivar.failure.isInstanceOf[IllegalArgumentException])
    assert(!ivar.isAssigned)
    assert(ivar.isCompleted)
    assert(ivar.isFailed)
    assert(!ivar.isUnassigned)
  }

  test("toRCell") {
    val emitter = new Events.Emitter[Int]
    val cell = emitter.toRCell
    assert(cell.isEmpty)
    intercept[NoSuchElementException] {
      cell()
    }
    emitter.react(7)
    assert(!cell.isEmpty)
    assert(cell() == 7)
  }

  test("possibly") {
    var seen = 0
    val emitter = new Events.Emitter[Int]
    emitter.possibly(0.5).on(seen += 1)
    for (_ <- 0 until 100) emitter.react(1)
  }

  class GetEmitter extends Events[Int] {
    def onReaction(obs: Observer[Int]) = {
      obs.react(7, null)
      Subscription.empty
    }
  }

  test("get") {
    val emitter = new Events.Emitter[Int]
    intercept[NoSuchElementException] {
      emitter.get
    }

    val getEmitter = new GetEmitter
    assert(getEmitter.get == 7)
  }

  test("sliding") {
    val emitter = new Events.Emitter[Int]
    val sliding = emitter.sliding(3)
    val seen = mutable.Buffer[Conc.Queue[Int]]()
    var done = false
    sliding.onEventOrDone(seen += _)({ done = true })
    emitter.react(1)
    assert(seen.last.toArray.toSeq == Seq(1))
    emitter.react(2)
    assert(seen.last.toArray.toSeq == Seq(2, 1))
    emitter.react(3)
    assert(seen.last.toArray.toSeq == Seq(3, 2, 1))
    emitter.react(4)
    assert(seen.last.toArray.toSeq == Seq(4, 3, 2))
    emitter.unreact()
    assert(done)
  }

  test("each") {
    val emitter = new Events.Emitter[Int]
    val each = emitter.each(3)
    val seen = mutable.Buffer[Int]()
    var done = false
    each.onEventOrDone(seen += _)({ done = true })
    emitter.react(1)
    assert(seen == Seq())
    assert(!done)
    emitter.react(11)
    emitter.react(17)
    assert(seen == Seq(17))
    assert(!done)
    emitter.react(19)
    emitter.react(2)
    assert(seen == Seq(17))
    emitter.react(23)
    assert(seen == Seq(17, 23))
    assert(!done)
    emitter.unreact()
    assert(done)
  }

  test("repeat") {
    val emitter = new Events.Emitter[Int]
    val repeat = emitter.repeat(3)()
    val seen = mutable.Buffer[Int]()
    var done = false
    repeat.onEventOrDone(seen += _)({ done = true })
    emitter.react(3)
    assert(seen == Seq(3, 3, 3))
    assert(!done)
    val emitterNeg = new Events.Emitter[Int]
    val repeatNeg = emitterNeg.repeat(3)(x => -x)
    repeatNeg.onEventOrDone(seen += _)({ done = true })
    emitterNeg.react(7)
    assert(seen == Seq(3, 3, 3, 7, -7, -7))
    assert(!done)
    emitterNeg.unreact()
    assert(done)
  }

  test("partition") {
    val emitter = new Events.Emitter[Int]
    val (odd, even) = emitter.partition(_ % 2 != 0)
    val odds = mutable.Buffer[Int]()
    val evens = mutable.Buffer[Int]()
    odd.onEventOrDone(odds += _)(odds.clear())
    even.onEventOrDone(evens += _)(evens.clear())
    emitter.react(1)
    assert(odds == Seq(1))
    assert(evens == Seq())
    emitter.react(7)
    assert(odds == Seq(1, 7))
    assert(evens == Seq())
    emitter.react(8)
    assert(odds == Seq(1, 7))
    assert(evens == Seq(8))
    emitter.unreact()
    assert(odds == Seq())
    assert(evens == Seq())
  }

}


class RCellSpec extends AnyFunSuite with Matchers {

  class ReactiveTest {
    val x = RCell(0)
    val y = RCell(0)
    val z = RCell(0)
    val w = RCell(0)
  }

  test("filtered") {
    val rt = new ReactiveTest
    val s = rt.x.filter {
      _ % 2 == 0
    }
    s.onEvent { case x =>
      assert(x % 2 == 0)
    }

    rt.x := 1
    rt.x := 2
  }

  def assertExceptionPropagated[S](
    create: Events[Int] => Events[S], effect: () => Unit
  ) {
    val e = new Events.Emitter[Int]
    val s = create(e)
    
    var nullptr = false
    var state = false
    var argument = false

    val h = s.onExcept {
      case e: IllegalStateException => state = true
      case e: NullPointerException => nullptr = true
      case _ => // ignore all the rest
    }

    val o = s.onExcept {
      case e: IllegalArgumentException => argument = true
      case _ => // ignore all the rest
    }

    e.except(new NullPointerException)
    e.react(1)
    e.react(2)
    e.except(new IllegalStateException)
    effect()
    e.except(new IllegalArgumentException)

    assert(nullptr)
    assert(state)
    assert(argument)
  }

  val noEffect = () => ()

  test("propagate the exception when filtered") {
    assertExceptionPropagated(_.filter(_ % 2 == 0), noEffect)
  }

  test("be mapped") {
    val e = RCell[Int](0)
    val s = e.map {
      _ + 4
    }
    var i = 0
    val a = s.onEvent { case x =>
      i match {
        case 0 => assert(x == 4)
        case 1 => assert(x == 7)
      }
      i += 1
    }

    e := 3
  }

  test("propagate the exception when mapped") {
    assertExceptionPropagated(_.map(_ + 1), noEffect)
  }

  test("be counted") {
    val e = new RCell[Int](0)
    val c = e.count
    val buffer = mutable.Buffer[Int]()
    val sub = c.onEvent(buffer += _)

    for (i <- 110 until 210) e := i
    assert(buffer == (1 to 101))
  }

  test("emit once") {
    val e = RCell(-1)
    val s = e.once
    val check = mutable.Buffer[Int]()
    val adds = s.onEvent(check += _)

    e := 1
    e := 2
    e := 3

    assert(check == Seq(-1))
  }

  test("not propagate exceptions after it emitted once") {
    val e = RCell(0)
    val s = e.dropWhile(_ == 0).once
    var exceptions = 0
    val h = s.onExcept { case _ => exceptions += 1 }

    e.except(new RuntimeException)
    assert(exceptions == 1)
    e.except(new RuntimeException)
    assert(exceptions == 2)
    e := 1
    e.except(new RuntimeException)
    assert(exceptions == 2)
  }

  test("be scanned past") {
    val cell = RCell(0)
    val s = cell.dropWhile(_ == 0).scanPast(List[Int]()) { (acc, x) =>
      x :: acc
    }
    val a = s onEvent { case xs =>
      assert(xs.reverse == Stream.from(1).take(xs.length))
    }

    cell := 1
    cell := 2
    cell := 3
    cell := 4
    cell := 5
  }

  test("propagate the exception when scanned past") {
    assertExceptionPropagated(_.scanPast(0)(_ + _), noEffect)
  }

  test("come after") {
    val e = RCell(0)
    val start = RCell(false)
    val buffer = mutable.Buffer[Int]()
    val s = (e.drop(1) after start.tail) onEvent {
      case x => buffer += x
    }

    e := 1
    e := 2
    e := 3
    start := true
    e := 4
    e := 5
    e := 6
    start := false
    e := 7
    e := 8
    buffer should equal (Seq(4, 5, 6, 7, 8))
  }

  test("propagate exceptions even before the first event") {
    val start = new Events.Emitter[Unit]
    assertExceptionPropagated(_ after start, () => start.react(()))
  }

  test("not propagate exceptions from that after the first event") {
    val start = new Events.Emitter[Unit]
    val exceptor = new Events.Emitter[Unit]
    val a = exceptor after start

    var state = false
    var arg = false
    val h = a onExcept {
      case e: IllegalStateException => state = true
      case e: IllegalArgumentException => arg = true
    }

    start.except(new IllegalStateException)
    assert(state)
    start.react(())
    start.except(new IllegalArgumentException)
    assert(!arg)
  }

  test("never come after") {
    val e = RCell(0)
    val start = new Events.Never[Int]
    val buffer = mutable.Buffer[Int]()
    val s = (e after start) onEvent { case x => buffer += x }

    e := 1
    e := 2
    e := 3
    buffer should equal (Seq())
  }

  test("propagate exceptions until the end event") {
    val end = new Events.Emitter[Unit]
    val e = new Events.Emitter[Int]
    val s = e.until(end)
    var exceptions = 0
    val h = s.onExcept { case _ => exceptions += 1 }

    e.except(new RuntimeException)
    assert(exceptions == 1)
    end.except(new RuntimeException)
    assert(exceptions == 2)
    e.except(new RuntimeException)
    assert(exceptions == 3)
    end.react(())
    e.except(new RuntimeException)
    assert(exceptions == 3)
    end.except(new RuntimeException)
    assert(exceptions == 3)
  }

  test("occur until") {
    val e = RCell(0)
    val end = RCell(false)
    val buffer = mutable.Buffer[Int]()
    val s = (e.tail until end.tail) onEvent { x => buffer += x }

    e := 1
    e := 2
    end := true
    e := 3
    end := false
    e := 4
    buffer should equal (Seq(1, 2))
  }

  test("union") {
    val xs = RCell(0)
    val ys = RCell(0)
    val buffer = mutable.Buffer[Int]()
    val s = (xs.tail union ys.tail) onEvent { case x => buffer += x }

    xs := 1
    ys := 11
    xs := 2
    ys := 12
    ys := 15
    xs := 7
    buffer should equal (Seq(1, 11, 2, 12, 15, 7))
  }

  test("propagate both exceptions to union") {
    val xs = new Events.Emitter[Int]
    val ys = new Events.Emitter[Int]
    val zs = xs union ys

    var state = false
    var arg = false
    val h = zs.onExcept {
      case e: IllegalStateException => state = true
      case e: IllegalArgumentException => arg = true
    }

    xs.except(new IllegalStateException)
    assert(state)
    ys.except(new IllegalArgumentException)
    assert(arg)
  }

  test("concat") {
    val xs = new Events.Emitter[Int]
    val closeXs = new Events.Emitter[Unit]
    val ys = new Events.Emitter[Int]
    val buffer = mutable.Buffer[Int]()
    val s = ((xs until closeXs) concat ys) onEvent { case x => buffer += x }

    xs react 1
    ys react 11
    xs react 2
    ys react 12
    ys react 15
    xs react 7
    closeXs.react(())
    buffer should equal (Seq(1, 2, 7, 11, 12, 15))
  }

  test("propagate both exceptions to concat") {
    val xs = new Events.Emitter[Int]
    val ys = new Events.Emitter[Int]
    val zs = xs concat ys

    var state = false
    var arg = false
    val h = zs onExcept {
      case e: IllegalStateException => state = true
      case e: IllegalArgumentException => arg = true
    }

    xs.except(new IllegalStateException)
    assert(state)
    ys.except(new IllegalArgumentException)
    assert(arg)
  }

  def testSynced() {
    val xs = new Events.Emitter[Int]
    val ys = new Events.Emitter[Int]
    val synced = (xs sync ys) { _ + _ }
    val buffer = mutable.Buffer[Int]()
    val s = synced onEvent { case x => buffer += x }

    for (i <- 0 until 200) xs react i
    for (j <- 200 to 51 by -1) ys react j
    buffer.size should equal (150)
    for (x <- buffer) x should equal (200)
  }

  test("be synced") {
    testSynced()
  }

  class Cell(var x: Int = 0)

  test("be muxed") {
    val cell = RCell[Events[Int]](new Signal.Const(0))
    val e1 = new Events.Emitter[Int]
    val e2 = new Events.Emitter[Int]
    val ints = cell.mux.toSignal(0)

    assert(ints() == 0, ints())
    cell := e1
    e1 react 10
    assert(ints() == 10, ints())
    e1 react 20
    assert(ints() == 20, ints())
    e2 react 30
    assert(ints() == 20, ints())
    cell := e2
    assert(ints() == 20, ints())
    e2 react 40
    assert(ints() == 40, ints())
    e1 react 50
    assert(ints() == 40, ints())
    e2 react 60
    assert(ints() == 60, ints())
  }

  test("be higher-order union") {
    val cell = RCell[Events[Int]](new Signal.Const(0))
    val e1 = new Events.Emitter[Int]
    val e2 = new Events.Emitter[Int]
    val e3 = new Events.Emitter[Int]
    val e4 = new Events.Emitter[Int]
    val closeE4 = new Events.Emitter[Unit]
    val buffer = mutable.Buffer[Int]()
    val s = cell.tail.union onEvent { case x => buffer += x }

    e1 react -1
    e2 react -2
    e3 react -3

    cell := e1
    e1 react 1
    e1 react 11
    e2 react -22
    e3 react -33
    cell := e2
    e1 react 111
    e2 react 2
    e3 react -333
    cell := e3
    e1 react 1111
    e2 react 22
    e3 react 3
    cell := e1
    e1 react 11111
    e2 react 222
    e3 react 33
    cell := (e4 until closeE4)
    e4 react 4
    closeE4.react(())
    e4 react -44
    buffer should equal (Seq(1, 11, 111, 2, 1111, 22, 3, 11111, 11111, 222, 33, 4))
  }

  test("be higher-order concat") {
    val cell = RCell[Events[Int]](new Signal.Const(0))
    val e1 = new Events.Emitter[Int]
    val closeE1 = new Events.Emitter[Unit]
    val e2 = new Events.Emitter[Int]
    val closeE2 = new Events.Emitter[Unit]
    val e3 = new Events.Emitter[Int]
    val closeE3 = new Events.Emitter[Unit]
    val e4 = new Events.Emitter[Int]
    val buffer = mutable.Buffer[Int]()
    val s = cell.tail.concat onEvent { x => buffer += x }

    e1 react -1
    e2 react -2
    e3 react -3

    cell := e1 until closeE1
    e1 react 1
    e1 react 11
    e2 react -22
    e3 react -33
    cell := e2 until closeE2
    e1 react 111
    e2 react 2
    e3 react -333
    cell := e3 until closeE3
    e1 react 1111
    e2 react 22
    e3 react 3
    closeE1.react(())
    closeE2.react(())
    e1 react -11111
    e2 react -222
    e3 react 33
    closeE3.react(())
    e3 react -333
    cell := e4
    e4 react 4

    buffer should equal (Seq(1, 11, 111, 1111, 2, 22, 3, 33, 4))
  }

  test("collect accurately") {
    val e = new Events.Emitter[String]
    val evens = e collect {
      case x if x.toInt % 2 == 0 => x
    }
    val observed = mutable.Buffer[String]()
    val emitSub = evens.onEvent(observed += _)

    for (i <- 0 until 100) e react i.toString

    observed should equal ((0 until 100 by 2).map(_.toString))
  }

  test("be taken while") {
    val e = new Events.Emitter[Int]
    val firstTen = e.takeWhile(_ < 10)
    val observed = mutable.Buffer[Int]()
    val emitSub = firstTen.onEvent(observed += _)

    for (i <- 0 until 20) e react i

    observed should equal (0 until 10)

    e react 5

    observed should equal (0 until 10)
  }

  test("be taken while until exception") {
    val e = new Events.Emitter[Int]
    val firstTen = e.takeWhile(x => {assert(x != 5); x < 10})
    val observed = mutable.Buffer[Int]()
    val emitSub = firstTen.onEvent(observed += _)

    intercept[TestFailedException] {
      for (i <- 0 until 20) e react i
    }

    observed should equal (0 until 5)
  }

  test("react to unreactions") {
    val e = new Events.Emitter[Int]
    val unreacted = e.done
    var events = 0
    var excepts = 0
    var unreactions = 0
    val observations = unreacted.onReaction(new Observer[Unit] {
      def react(u: Unit, hint: Any) {
        assert(unreactions == 0)
        events += 1
      }
      def except(t: Throwable) = excepts += 1
      def unreact() {
        assert(events == 1)
        unreactions += 1
      }
    })

    for (i <- 0 until 10) e react i

    assert(events == 0)
    assert(excepts == 0)
    assert(unreactions == 0)

    e.except(new Exception)

    assert(events == 0)
    assert(excepts == 1)
    assert(unreactions == 0)

    e.unreact()

    assert(events == 1)
    assert(excepts == 1)
    assert(unreactions == 1)
  }

  case object TestException extends Exception

  test("throw from an onEvent") {
    var num = 0
    val e = new Events.Emitter[Int]
    val f = e.onEvent(num += _)
    e.react(2)
    assert(num == 2)
    intercept[UnhandledException] {
      e.except(TestException)
    }
  }

  test("throw from onDone") {
    val e = new Events.Emitter[Int]
    val u = e.map[Int](_ => throw TestException).onDone(() => {})
    intercept[UnhandledException] {
      e.except(TestException)
    }
  }

  test("throw from onExcept") {
    val e = new Events.Emitter[Int]
    val h = e.onExcept { case _ => throw TestException }
    intercept[TestException.type] {
      e.except(new Exception)
    }
  }

  test("throw from onReaction") {
    val e = new Events.Emitter[Int]
    val o = e.onReaction(new Observer[Int] {
      def react(x: Int, hint: Any) {
        throw TestException
      }
      def except(t: Throwable) {
        throw TestException
      }
      def unreact() {
        throw TestException
      }
    })
    intercept[TestException.type] {
      e.react(1)
    }
    intercept[TestException.type] {
      e.except(new Exception)
    }
    intercept[TestException.type] {
      e.unreact()
    }
  }

  test("throw from onReactUnreact") {
    val e = new Events.Emitter[Int]
    val o = e.onEventOrDone(x => throw TestException)(throw TestException)
    intercept[TestException.type] {
      e.react(1)
    }
    intercept[TestException.type] {
      e.unreact()
    }
  }

  test("throw from onMatch") {
    val e = new Events.Emitter[String]
    intercept[TestException.type] {
      val o = e.onMatch { case "1" => throw TestException }
      e.react("1")
    }
    intercept[TestException.type] {
      val o = e.map[String](_ => throw TestException).onMatch { case _ => }
      e.react("1")
    }
  }

  test("throw from on") {
    val e = new Events.Emitter[String]
    intercept[UnhandledException] {
      val o = e on {}
      e.except(TestException)
    }
  }

  test("recover from errors") {
    val e = new Events.Emitter[String]
    val buffer = mutable.Buffer[String]()
    e.recover({
      case e: Exception => e.getMessage
    }).onEvent(buffer += _)
    e.except(new Exception("false positive"))
    buffer.size should equal (1)
    assert(buffer.contains("false positive"))
  }

  test("ignore all incoming exceptions") {
    val e = new Events.Emitter[String]
    val buffer = mutable.Buffer[Throwable]()
    val recovered = e.ignoreExceptions.onExcept {
      case t => buffer += t
    }
    e.except(new Exception)
    buffer.size should equal (0)
  }

  test("empty cell") {
    val c = RCell[Int]
    assert(c.isEmpty)
    c := 17
    assert(!c.isEmpty)
    assert(c() == 17)
  }
}


class EventsCheck extends Properties("Events") with ExtendedProperties {

  val sizes = detChoose(0, 1000)

  property("should register observers") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val buffer = mutable.Buffer[Int]()
      val emitter = new Events.Emitter[String]
      for (i <- 0 until size) emitter.onEvent(x => buffer += i)
  
      emitter.react("ok")
  
      buffer.toSet == (0 until size).toSet
    }
  }

  property("should deregister observers") = forAllNoShrink(sizes, sizes) { (add, rem) =>
    stackTraced {
      val buffer = mutable.Buffer[Int]()
      val emitter = new Events.Emitter[String]
      val subs = for (i <- 0 until add) yield emitter.onEvent(x => buffer += i)
      for (i <- 0 until math.min(add, rem)) subs(i).unsubscribe()
  
      emitter.react("ok")
  
      buffer.toSet == (math.min(add, rem) until add).toSet
    }
  }

}
