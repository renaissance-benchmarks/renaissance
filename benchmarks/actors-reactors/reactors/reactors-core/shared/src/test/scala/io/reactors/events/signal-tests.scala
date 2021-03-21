package io.reactors
package events



import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import org.scalacheck.Gen.choose
import org.scalatest._
import io.reactors.test._
import scala.collection._
import org.scalatest.funsuite.AnyFunSuite



class SignalSpec extends AnyFunSuite {

  class TestEmitter[T] extends Events.Emitter[T] {
    var unsubscriptionCount = 0
    override def onReaction(obs: Observer[T]) = new Subscription.Composite(
      super.onReaction(obs),
      new Subscription {
        def unsubscribe() = unsubscriptionCount += 1
      }
    )
  }

  test("changes") {
    val buffer = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[Int]
    emitter.toSignal(0).changes.onEvent(buffer += _)

    emitter.react(3)
    emitter.react(3)
    emitter.react(5)
    emitter.react(7)
    emitter.react(7)
    emitter.react(11)
    assert(buffer == Seq(3, 5, 7, 11))
  }

  test("diffPast") {
    val buffer = mutable.Buffer[Int]()
    val emitter = new Events.Emitter[Int]
    emitter.toSignal(0).diffPast(_ - _).onEvent(buffer += _)

    emitter.react(3)
    assert(buffer == Seq(0, 3))
    emitter.react(3)
    assert(buffer == Seq(0, 3, 0))
    emitter.react(5)
    assert(buffer == Seq(0, 3, 0, 2))
    emitter.react(11)
    assert(buffer == Seq(0, 3, 0, 2, 6))
    emitter.react(19)
    assert(buffer == Seq(0, 3, 0, 2, 6, 8))
    emitter.unreact()
  }

  test("zip") {
    var done = false
    val buffer = mutable.Buffer[Int]()
    val e0 = new Events.Emitter[Int]
    val e1 = new Events.Emitter[Int]
    val zip = (e0.toSignal(0) zip e1.toSignal(0))(_ + _)
    zip.onEvent(buffer += _)
    zip.onDone({ done = true })

    e0.react(3)
    assert(buffer == Seq(0, 3))
    e1.react(5)
    assert(buffer == Seq(0, 3, 8))
    e1.react(7)
    assert(buffer == Seq(0, 3, 8, 10))
    e1.react(11)
    assert(buffer == Seq(0, 3, 8, 10, 14))
    e0.react(19)
    assert(buffer == Seq(0, 3, 8, 10, 14, 30))
    assert(!done)
    e1.unreact()
    assert(buffer == Seq(0, 3, 8, 10, 14, 30))
    assert(!done)
    e0.unreact()
    assert(done)
    e0.react(23)
    assert(buffer == Seq(0, 3, 8, 10, 14, 30))
  }

  test("past2") {
    var last = (0, 0)
    val emitter = new Events.Emitter[Int]
    emitter.toSignal(0).past2(0).onEvent(last = _)

    emitter.react(3)
    assert(last == (0, 3))
    emitter.react(7)
    assert(last == (3, 7))
  }

  test("aggregate") {
    val x = new Events.Emitter[Int]
    val y = new Events.Emitter[Int]
    val z = new Events.Emitter[Int]
    val w = new Events.Emitter[Int]
    val aggregate = Signal.aggregate(
      x.toSignal(1),
      y.toSignal(2),
      z.toSignal(3),
      w.toSignal(4)
    )(0)(_ + _)

    assert(aggregate() == 10)
    x.react(10)
    assert(aggregate() == 19)
    y.react(20)
    assert(aggregate() == 37)
    z.react(30)
    assert(aggregate() == 64)
    w.react(40)
    assert(aggregate() == 100)

    aggregate.unsubscribe()

    x.react(11)
    assert(aggregate() == 100)
  }

  test("be constant") {
    val s = new Signal.Const(1)
    assert(s() == 1)
  }

  class ReactiveTest {
    val x = RCell(0)
    val y = RCell(0)
    val z = RCell(0)
    val w = RCell(0)
  }

  test("be mapped") {
    val rt = new ReactiveTest
    val s = rt.x.map {
      _ + 1
    }
    val a = s.tail onEvent { case x =>
      assert(x == 2)
    }

    rt.x := 1
  }

  test("be diffed past") {
    val cell = RCell(1)
    val diff = cell.diffPast(_ - _)
    var total = 0
    val a = diff.tail onEvent { case d =>
      total += 2
      assert(d == 2)
    }

    cell := 3
    cell := 5
    cell := 7
    cell := 9

    assert(total == 8)
  }

  test("be zipped") {
    var updates = 0
    val rt = new ReactiveTest
    val sp1 = rt.x map { x =>
      x + 1
    } toSignal(1)
    val sp2 = sp1 map {
      _ + 1
    } toSignal(2)
    val sdiff = (sp2 zip sp1) { (x, y) =>
      updates += 1
      x - y
    } toSignal(-1)

    rt.x := rt.x() + 1
    assert(sdiff() == 1)
    rt.x := rt.x() + 1
    assert(sdiff() == 1)
  }

  test("be zipped on constant signals") {
    val c1 = new Signal.Const(7)
    val c2 = new Signal.Const(19)
    val s = (c1 zip c2)(_ + _)
    assert(s() == 26)
  }

  test("reflect changes") {
    val rc = RCell(0)
    val buffer = mutable.Buffer[Int]()
    val subscription = rc.changes.onEvent {
      case x => buffer += x
    }

    rc := 0
    rc := 1
    rc := 2
    rc := 2
    rc := 2
    rc := 3
    rc := 3
    rc := 4
    assert(buffer == Seq(1, 2, 3, 4))
  }

  test("be aggregated") {
    val rt = new ReactiveTest
    rt.x := 1
    rt.y := 2
    rt.z := 3
    rt.w := 4
    val aggregated = Signal.aggregate(rt.x, rt.y, rt.z, rt.w)(0) {
      _ + _
    }

    assert(aggregated() == 10)
    rt.x := 10
    assert(aggregated() == 19)
    rt.y := 20
    assert(aggregated() == 37)
    rt.z := 30
    assert(aggregated() == 64)
    rt.w := 40
    assert(aggregated() == 100)
  }

  test("triple zip") {
    val e1 = new Events.Emitter[String]
    val e2 = new Events.Emitter[String]
    val e3 = new Events.Emitter[String]
    val s1 = e1.toSignal("")
    val s2 = e2.toSignal("")
    val s3 = e3.toSignal("")
    val buffer = mutable.Buffer[(String, String, String)]()
    val f = (x: String, y: String, z: String) => (x, y, z)
    val zipped = ((s1 zip s2)((_, _)) zip s3) {
      (p1, p2) => f(p1._1, p1._2, p2)
    }
    val sub = zipped.onEvent(buffer += _)
    e1 react "a"
    e2 react "b"
    e3 react "c"
    val expected = Seq(
      ("", "", ""),
      ("a", "", ""),
      ("a", "b", ""),
      ("a", "b", "c")
    )
    assert(buffer == expected)
  }

  test("syncWith") {
    val e1 = new Events.Emitter[String]
    val e2 = new Events.Emitter[String]
    val s1 = e1.toSignal("1")
    val s2 = e2.toSignal("2")
    val synced = (s1 syncWith s2)((_, _))
    val buffer = mutable.Buffer[(String, String)]()
    synced.onEvent(buffer += _)
    e2.react("22")
    buffer += synced()
    e1.react("11")
    assert(buffer == Seq(("1", "2"), ("1", "2"), ("11", "22")))
  }

  test("zip many") {
    val e1 = new Events.Emitter[Char]
    val e2 = new Events.Emitter[Char]
    val e3 = new Events.Emitter[Char]
    val sig1 = e1.toSignal('d')
    val sig2 = e2.toSignal('c')
    val sig3 = e3.toSignal('e')
    val zipped = Signal.zip(sig1, sig2, sig3) { ss => () =>
      ss.find(s => s().isUpper).map(_()).getOrElse('?')
    }
    var done = false
    zipped.onDone({ done = true })
    assert(zipped() == '?')
    e2.react('f')
    assert(zipped() == '?')
    e3.react('A')
    assert(zipped() == 'A')
    e1.react('g')
    assert(zipped() == 'A')
    e1.react('B')
    assert(zipped() == 'B')
    e1.react('h')
    assert(zipped() == 'A')
    e1.unreact()
    assert(zipped() == 'A')
    e1.unreact()
    assert(zipped() == 'A')
    assert(!done)
    e2.react('C')
    assert(zipped() == 'C')
    assert(!done)
    e2.unreact()
    assert(zipped() == 'C')
    assert(!done)
    e3.unreact()
    assert(zipped() == 'C')
    assert(done)
  }
}
