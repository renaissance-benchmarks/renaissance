package io.reactors
package protocol.algo



import io.reactors.test._
import org.scalatest._
import org.scalatest.concurrent.AsyncTimeLimitedTests
import scala.collection._
import scala.concurrent._
import scala.concurrent.ExecutionContext
import scala.concurrent.duration._
import org.scalatest.funsuite.AnyFunSuite



class AlgoSpec extends AnyFunSuite {
  test("reservoir sampling, no events") {
    val e = new Events.Emitter[Int]
    val sample = e.sampleReservoir(5)
    e.unreact()
    assert(sample().length == 0)
  }

  test("reservoir sampling, less than k") {
    val e = new Events.Emitter[Int]
    val sample = e.sampleReservoir(5)
    e.react(7)
    e.react(17)
    e.unreact()
    assert(sample().toSeq == Seq(7, 17))
  }

  test("reservoir sampling, more than k") {
    val e = new Events.Emitter[Int]
    val sample = e.sampleReservoir(5)
    val elems = (0 until 16)
    for (i <- elems) e.react(i)
    e.unreact()
    assert(sample().toSeq.length == 5)
    assert(sample().toSeq.forall(x => elems.toSet.contains(x)))
    assert(sample().distinct.length == 5)
  }
  test("weighted sampling, no events") {
    val e = new Events.Emitter[Double]
    val sample = e.sampleWeighted(5, x => x)
    e.unreact()
    assert(sample().length == 0)
  }

  test("weighted sampling, less than k") {
    val e = new Events.Emitter[Double]
    val sample = e.sampleWeighted(5, x => x)
    e.react(7.0)
    e.react(17.0)
    e.unreact()
    assert(sample().toSet == Set(7.0, 17.0))
  }

  test("weighted sampling, more than k") {
    val e = new Events.Emitter[String]
    val sample = e.sampleWeighted(5, s => s.length.toDouble)
    val elems = (0 until 16).map(i => (i * i).toString)
    for (s <- elems) e.react(s)
    e.unreact()
    assert(sample().toSeq.length == 5)
    assert(sample().toSeq.forall(x => elems.toSet.contains(x)))
    assert(sample().distinct.length == 5)
  }
}
