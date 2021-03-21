package io.reactors.common



import scala.collection._
import scala.reflect.ClassTag
import Conc._
import ConcRope._
import Conqueue._



trait ConcSnippets {

  def concList[T](elems: Seq[T]): Conc[T] = {
    var xs: Conc[T] = Empty
    for (x <- elems) {
      xs <>= new Single(x)
    }
    xs
  }

  def concRope[T: ClassTag](elems: Seq[T]): Conc[T] = {
    var xs: Conc[T] = Empty
    for (x <- elems) xs = xs rappend x
    xs
  }

  def concChunkRope[T: ClassTag](elems: Seq[T], k: Int): Conc[T] = {
    val xs = new ConcBuffer[T](k)
    for (x <- elems) xs += x
    xs.extractConc()
  }

  def conqueue[T: ClassTag](elems: Seq[T]): Conqueue[T] = {
    var xs: Conqueue[T] = Conqueue.Tip(Zero)
    for (x <- elems) xs = xs :+ x
    xs
  }

  def toSeq[T](xs: Conc[T]): Seq[T] = {
    val buffer = mutable.Buffer[T]()
    for (x <- xs) {
      buffer += x
    }
    buffer
  }

  def checkInvs(xs: Conc[Int]): Boolean = xs match {
    case left <> right =>
      assert(math.abs(left.level - right.level) <= 1)
      checkInvs(left) && checkInvs(right)
    case Append(l @ Append(_, lr), r) =>
      assert(lr.level > r.level)
      checkInvs(l) && checkInvs(r)
    case Append(l, r) =>
      assert(l.level > r.level)
      checkInvs(l) && checkInvs(r)
    case _ =>
      true
  }

  def checkConqueueInvs(conq: Conc[Int], level: Int): Boolean =
    (conq: Conc[Int] @unchecked) match {
      case Lazy(_, q, _) =>
        assert(level == 0)
        checkConqueueInvs(q, 0)
      case s: Spine[Int] =>
        if (s.lwing == Zero || s.rwing == Zero) {
          assert(false, "Evaluated Spine cannot contain Zero.")
        }
        checkConqueueInvs(s.lwing, level) &&
        checkConqueueInvs(s.rwing, level) &&
        checkConqueueInvs(s.rear, level + 1)
      case Tip(tip) =>
        checkConqueueInvs(tip, level)
      case Zero =>
        true
      case One(_1) =>
        assert(_1.level == level, s"levels: ${_1.level} vs $level")
        checkInvs(_1)
      case Two(_1, _2) =>
        assert(_1.level == level)
        assert(_2.level == level)
        checkInvs(_1) && checkInvs(_2)
      case Three(_1, _2, _3) =>
        assert(_1.level == level)
        assert(_2.level == level)
        assert(_3.level == level)
        checkInvs(_1) && checkInvs(_2) && checkInvs(_3)
      case Four(_1, _2, _3, _4) =>
        assert(_1.level == level)
        assert(_2.level == level)
        assert(_3.level == level)
        assert(_4.level == level)
        checkInvs(_1) && checkInvs(_2) && checkInvs(_3) && checkInvs(_4)
    }

  def testConcatCorrectness(n: Int, m: Int) = {
    var xs: Conc[Int] = concList(0 until n)
    var ys: Conc[Int] = concList(0 until m)

    toSeq(xs <> ys) == ((0 until n) ++ (0 until m))
  }

  def testConcatBalance(n: Int, m: Int) = {
    var xs: Conc[Int] = concList(0 until n)
    var ys: Conc[Int] = concList(0 until m)

    checkInvs(xs <> ys)
  }

  def testApply(n: Int) = {
    var xs: Conc[Int] = concList(0 until n)
    val checks = for (i <- 0 until n) yield i == xs(i)

    checks.forall(_ == true)
  }

  def testUpdate(n: Int) = {
    var xs: Conc[Int] = concList(0 until n)

    for (i <- 0 until n) xs = xs.update(i, -i)

    val checks = for (i <- 0 until n) yield -i == xs(i)

    checks.forall(_ == true)
  }

  def testRopeUpdate(n: Int) = {
    var xs: Conc[Int] = concRope(0 until n)

    for (i <- 0 until n) xs = xs.update(i, -i)

    val checks = for (i <- 0 until n) yield -i == xs(i)

    checks.forall(_ == true)
  }

  def testConqueueUpdate(n: Int) = {
    var xs: Conc[Int] = conqueue(0 until n)

    for (i <- 0 until n) xs = xs.update(i, -i)

    val checks = for (i <- 0 until n) yield -i == xs(i)

    checks.forall(_ == true)
  }

  def compare(sample: Int, xs: Conc[Int], ys: Seq[Int]) {
    val xsb = mutable.Buffer[Int]()
    for (x <- xs) xsb += x
    println("----------")
    println(sample)
    println(ys)
    println(xsb)
  }

  def testInsert(size: Int, samples: Int, seed: Int) = {
    var xs: Conc[Int] = concList(0 until size)
    val buffer = mutable.Buffer[Int]() ++ (0 until size)

    for (i <- 0 until samples) {
      val sample = (seed + i * 179) % (xs.size + 1)
      xs = xs.insert(sample, -sample - 1)
      buffer.insert(sample, -sample - 1)
    }

    buffer == toSeq(xs)
  }

  def testAppendCorrectness(size: Int, appends: Int) = {
    var xs = concList(0 until size)
    for (i <- 0 until appends) xs = xs rappend i

    val same = toSeq(xs) == ((0 until size) ++ (0 until appends))
    val sameNorm = toSeq(xs.normalized) == ((0 until size) ++ (0 until appends))
    same && sameNorm
  }

  def testAppendBalance(size: Int, appends: Int) = {
    var xs = concList(0 until size)
    for (i <- 0 until appends) xs = xs rappend i

    checkInvs(xs) && checkInvs(xs.normalized)
  }

  def testSplit(xs: Conc[Int], at: Int) = {
    val size = xs.size
    val (left, right) = xs.split(at)

    val equal = (toSeq(left) ++ toSeq(right)) == (0 until size)

    checkInvs(left) &&
    checkInvs(right) &&
    equal
  }

}




