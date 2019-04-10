/* scala-stm - (c) 2009-2014, Stanford University, PPL */

package scala.concurrent.stm
package skel

import org.scalatest.FunSuite

class AtomicArraySuite extends FunSuite {

  test("Unit") {
    runIsolatedTest(List((), (), ()))
  }

  test("Boolean") {
    runIsolatedTest(List(false, true, false, true))
  }

  test("Byte") {
    runIsolatedTest(Array(0 : Byte, 1 : Byte, 2 : Byte))
  }

  test("Short") {
    runIsolatedTest(List(0 : Short, 1 : Short, 2 : Short))
  }

  test("Char") {
    runIsolatedTest("abcdefg".toSeq)
  }

  test("Int") {
    runIsolatedTest(100 until 200)
  }

  test("Float") {
    runIsolatedTest((20 to 30) map { _ * 0.1f })
  }

  test("Long") {
    runIsolatedTest((100 until 200) map { _ - 100L * Int.MaxValue })
  }

  test("Double") {
    runIsolatedTest((10 until 20) map { math.exp(_) })
  }

  test("AnyRef") {
    runIsolatedTest((10 until 20) map { i => ("x" + i) : AnyRef })
  }

  test("Any") {
    runIsolatedTest[Any]((10 until 20) map { i => i : Any })
  }

  def runIsolatedTest[A](values: Seq[A])(implicit am: ClassManifest[A]) {
    val singleton = AtomicArray[A](1)
    if (am != implicitly[ClassManifest[Unit]])
      assert(singleton(0) === am.newArray(1)(0))

    val aa = AtomicArray(values)
    for (i <- 0 until aa.length)
      assert(values(i) === aa(i))
    for (i <- 0 until aa.length)
      aa(i) = values(aa.length - 1 - i)
    for (i <- 0 until aa.length)
      assert(aa(i) === values(aa.length - 1 - i))
    for (i <- 0 until aa.length) {
      if (aa(i) == values(0)) {
        assert(aa.compareAndSet(i, values(0), values(i)))
        assert(aa(i) === values(i))
      } else {
        assert(!aa.compareAndSet(i, values(0), values(i)))
        assert(aa(i) === values(aa.length - 1 - i))
      }
    }
    for (i <- 0 until aa.length)
      assert(aa(i) === aa.getAndTransform(i)( v => v ))
    for (i <- 0 until aa.length) {
      val prev = aa(i)
      assert(aa.swap(i, values(i)) === prev)
    }

    intercept[IndexOutOfBoundsException] {
      aa(-1)
    }
    intercept[IndexOutOfBoundsException] {
      aa(-1) = aa(0)
    }
    intercept[IndexOutOfBoundsException] {
      aa(aa.length)
    }
    intercept[IndexOutOfBoundsException] {
      aa(aa.length) = aa(0)
    }
    intercept[IndexOutOfBoundsException] {
      aa.compareAndSet(-1, aa(0), aa(0))
    }
    intercept[IndexOutOfBoundsException] {
      aa.compareAndSet(aa.length, aa(0), aa(0))
    }
    intercept[IndexOutOfBoundsException] {
      aa(Int.MinValue)
    }
    intercept[IndexOutOfBoundsException] {
      aa(Int.MaxValue)
    }

    val copy = aa.clone
    for (i <- 0 until aa.length)
      assert(copy(i) === aa(i))

    val str0 = aa map { _.toString }
    val str: AtomicArray[String] = str0
    for (i <- 0 until aa.length)
      assert(aa(i).toString === str(i))

    val seq0 = aa.toList
    for (i <- 0 until aa.length)
      assert(aa(i) == seq0(i))

    val seq1 = aa.iterator.toList
    for (i <- 0 until aa.length)
      assert(aa(i) == seq1(i))

    val bb = aa ++ seq0
    assert(bb.length === aa.length * 2)
    for (i <- 0 until aa.length) {
      assert(aa(i) === bb(i))
      assert(aa(i) === bb(i + aa.length))
    }

    assert(aa.toString.startsWith("AtomicArray"))
  }
}
