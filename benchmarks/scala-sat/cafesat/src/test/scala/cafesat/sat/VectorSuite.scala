package cafesat.sat

import org.scalatest.funsuite.AnyFunSuite

class VectorSuite extends AnyFunSuite {

  test("init with append") {
    val v1 = new Vector[Int](50)
    assert(v1.size === 0)
    v1.append(3)
    assert(v1.size === 1)
    assert(v1(0) === 3)
    v1.append(5)
    assert(v1.size === 2)
    assert(v1(0) === 3)
    assert(v1(1) === 5)
    v1.append(5)
    assert(v1.size === 3)
    assert(v1(0) === 3)
    assert(v1(1) === 5)
    assert(v1(2) === 5)

    val v2 = new Vector[Int](50)
    v2.append(1)
    assert(v2.size === 1)
    assert(v2(0) === 1)
    v2.append(2)
    assert(v2.size === 2)
    assert(v2(0) === 1)
    assert(v2(1) === 2)
    v2.append(3)
    assert(v2.size === 3)
    assert(v2(0) === 1)
    assert(v2(1) === 2)
    assert(v2(2) === 3)
  }

  test("automatic allocate") {
    val v1 = new Vector[Int](2)
    v1.append(3)
    assert(v1.size === 1)
    assert(v1(0) === 3)
    v1.append(5)
    assert(v1.size === 2)
    assert(v1(0) === 3)
    assert(v1(1) === 5)
    v1.append(5)
    assert(v1.size === 3)
    assert(v1(0) === 3)
    assert(v1(1) === 5)
    assert(v1(2) === 5)

    val v2 = new Vector[Int](2)
    v2.append(1)
    assert(v2.size === 1)
    assert(v2(0) === 1)
    v2.append(2)
    assert(v2.size === 2)
    assert(v2(0) === 1)
    assert(v2(1) === 2)
    v2.append(3)
    assert(v2.size === 3)
    assert(v2(0) === 1)
    assert(v2(1) === 2)
    assert(v2(2) === 3)

    val v3 = new Vector[Int](2)
    v3.append(1)
    v3.append(2)
    v3.append(3)
    v3.append(5)
    v3.append(1)
    v3.append(0)
    v3.append(2)
    v3.append(3)
    assert(v3.size === 8)
    assert(v3(0) === 1)
    assert(v3(1) === 2)
    assert(v3(2) === 3)
    assert(v3(3) === 5)
    assert(v3(4) === 1)
    assert(v3(5) === 0)
    assert(v3(6) === 2)
    assert(v3(7) === 3)
  }


  test("update") {
    val v1 = new Vector[Int](50)
    v1.append(3)
    v1.append(5)
    v1.append(5)
    assert(v1(0) === 3)
    v1(0) = 8
    assert(v1(0) === 8)
    assert(v1(2) === 5)
    v1(2) = 0
    assert(v1(2) === 0)
    assert(v1.size === 3)
  }

  test("remove") {
    val v1 = new Vector[Int](50)
    v1.append(1)
    v1.append(2)
    v1.append(3)
    assert(v1.size === 3)
    v1.remove(1)
    assert(v1.size === 2)
    assert(v1(0) === 2)
    assert(v1(1) === 3)
  }

  test("contains") {
    val v1 = new Vector[Int](50)
    v1.append(1)
    v1.append(2)
    v1.append(3)
    assert(v1.contains(2))
    assert(v1.contains(1))
    assert(v1.contains(3))
    assert(!v1.contains(5))
    assert(!v1.contains(0))
    assert(v1.contains(2))
  }

  test("shrink") {
    val v1 = new Vector[Int](50)
    v1.append(1)
    v1.append(2)
    v1.append(3)
    v1.append(5)
    v1.append(1)
    v1.append(0)
    v1.append(2)
    v1.append(3)
    assert(v1.size === 8)
    v1.shrink(5)
    assert(v1.size === 3)
    assert(v1(0) === 1)
    assert(v1(1) === 2)
    assert(v1(2) === 3)
  }
}
