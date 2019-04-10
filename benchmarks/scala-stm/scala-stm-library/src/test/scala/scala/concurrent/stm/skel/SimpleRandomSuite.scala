/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm
package skel

import org.scalatest.FunSuite

class SimpleRandomSuite extends FunSuite {

  test("nextInt") {
    val f = new SimpleRandom
    val rand = new scala.util.Random
    var s = 0
    for (i <- 0 until 100000) {
      s |= SimpleRandom.nextInt
      s |= f.nextInt
    }
    assert(s != 0)
  }

  test("nextInt(n) in range") {
    val f = new SimpleRandom
    val rand = new scala.util.Random
    for (i <- 0 until 100000) {
      val n = rand.nextInt(Int.MaxValue - 1) + 1
      val gr = SimpleRandom.nextInt(n)
      assert(gr >= 0 && gr < n)
      val lr = f.nextInt(n)
      assert(lr >= 0 && lr < n)
    }
  }

  test("clone") {
    val f1 = new SimpleRandom
    for (i <- 0 until 1000)
      f1.nextInt
    val f2 = f1.clone
    for (i <- 0 until 1000)
      assert(f1.nextInt(9999) === f2.nextInt(9999))
  }

  test("seeded") {
    val f1 = new SimpleRandom(100)
    val f2 = new SimpleRandom(100)
    for (i <- 0 until 1000)
      assert(f1.nextInt === f2.nextInt)
  }

  test("global SimpleRandom distribution") {
    val buckets = new Array[Int](100)
    for (i <- 0 until 100000)
      buckets(SimpleRandom.nextInt(buckets.length)) += 1
    for (b <- buckets)
      assert(b > 0)
  }

  test("local SimpleRandom distribution") {
    val f = new SimpleRandom
    val buckets = new Array[Int](100)
    for (i <- 0 until 100000)
      buckets(f.nextInt(buckets.length)) += 1
    for (b <- buckets)
      assert(b > 0)
  }
}