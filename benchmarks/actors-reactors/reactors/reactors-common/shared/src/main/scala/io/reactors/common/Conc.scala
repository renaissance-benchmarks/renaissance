package io.reactors.common



import io.reactors.Arrayable
import scala.annotation.unchecked
import scala.annotation.tailrec
import scala.annotation.switch
import scala.reflect.ClassTag
import scala.runtime.ObjectRef



sealed trait Conc[@specialized(Int, Long, Float, Double) +T] {
  def level: Int
  def size: Int
  def left: Conc[T]
  def right: Conc[T]
  def normalized = this
}


case class <>[+T](left: Conc[T], right: Conc[T]) extends Conc[T] {
  val level = 1 + math.max(left.level, right.level)
  val size = left.size + right.size
}


object Conc {

  sealed trait Leaf[T] extends Conc[T] {
    def left = unsupported("Leaves do not have children.")
    def right = unsupported("Leaves do not have children.")
  }
  
  case object Empty extends Leaf[Nothing] {
    def level = 0
    def size = 0
  }
  
  class Single[@specialized(Int, Long, Float, Double) T](val x: T)
  extends Leaf[T] {
    def level = 0
    def size = 1
    override def toString = s"Single($x)"
  }
  
  class Chunk[@specialized(Int, Long, Float, Double) T](
    val array: Array[T], val size: Int, val k: Int
  ) extends Leaf[T] {
    def level = 0
    override def toString = s"Chunk(${array.mkString("", ", ", "")}; $size; $k)"
  }

  def reverseQueueForeach[
    @specialized(Int, Long, Float, Double) T,
    @specialized(Int, Long, Float, Double, Unit) U
  ](xs: Conc[T], f: T => U): Unit = (xs: @unchecked) match {
    case left <> right =>
      reverseQueueForeach(right, f)
      reverseQueueForeach(left, f)
    case s: Single[T] @unchecked =>
      f(s.x)
    case Empty =>
    case ConcRope.Append(left, right) =>
      reverseQueueForeach(right, f)
      reverseQueueForeach(left, f)
    case ConcRope.Prepend(left, right) =>
      reverseQueueForeach(right, f)
      reverseQueueForeach(left, f)
    case _ =>
      invalid("All cases should have been covered: " + xs.getClass)
  }

  def reverseQueueApply[@specialized(Int, Long, Float, Double) T](
    xs: Conc[T], i: Int
  ): T = {
    (xs: @unchecked) match {
      case _ <> right if i < right.size =>
        reverseQueueApply(right, i)
      case left <> right =>
        reverseQueueApply(left, i - right.size)
      case s: Single[T] @unchecked => s.x
      case ConcRope.Append(_, right) if i < right.size =>
        reverseQueueApply(right, i)
      case ConcRope.Append(left, right) =>
        reverseQueueApply(left, i - right.size)
      case ConcRope.Prepend(_, right) if i < right.size =>
        reverseQueueApply(right, i)
      case ConcRope.Prepend(left, right) =>
        reverseQueueApply(left, i - right.size)
      case _ =>
        invalid("All cases should have been covered: " + xs.getClass)
    }
  }

  class Queue[@specialized(Int, Long, Float, Double) T](
    private[reactors] val left: Conc[T],
    private[reactors] val right: Conc[T]
  ) {
    import ConcRope.Append
    import ConcRope.Prepend

    def this() = this(Empty, Empty)

    def size: Int = left.size + right.size

    def isEmpty: Boolean = size == 0

    def head: T = {
      @tailrec def find(c: Conc[T]): T = c match {
        case Append(l, r) => find(r)
        case Prepend(l, r) => find(r)
        case l <> r => find(r)
        case s: Single[T] @unchecked => s.x
        case _ => ???
      }
      if (size == 0) throw new IllegalStateException("<empty>.head")
      if (right.size > 0) find(right)
      else find(left)
    }

    def foreach[@specialized(Int, Long, Float, Double, Unit) U](f: T => U): Unit = {
      reverseQueueForeach(right, f)
      reverseQueueForeach(left, f)
    }

    def last: T = {
      @tailrec def find(c: Conc[T]): T = c match {
        case Append(l, r) => find(l)
        case Prepend(l, r) => find(l)
        case l <> r => find(l)
        case s: Single[T] @unchecked => s.x
        case _ => ???
      }
      if (size == 0) throw new IllegalStateException("<empty>.last")
      if (left.size > 0) find(left)
      else find(right)
    }

    def apply(idx: Int): T = {
      if (idx < 0 || idx >= size) throw new IndexOutOfBoundsException(s"$idx")
      if (idx < right.size) reverseQueueApply(right, idx)
      else reverseQueueApply(left, idx - right.size)
    }

    def enqueue(x: T): Queue[T] = {
      new Queue(left, ConcRope.append(right, new Single(x)))
    }

    def dequeue(): Queue[T] = {
      if (size == 0) throw new IllegalStateException("<empty>.dequeue")
      if (left.size > 0) new Queue(ConcRope.unprependDirect(left), right)
      else {
        right.normalized match {
          case l <> r =>
            new Queue(ConcRope.unprependDirect(l), r)
          case s: Single[T] @unchecked =>
            new Queue(Empty, Empty)
          case _ => ???
        }
      }
    }

    def toArray(implicit a: Arrayable[T]): Array[T] = {
      val array = a.newRawArray(size)
      var i = 0
      for (x <- this) {
        array(i) = x
        i += 1
      }
      array
    }
  }

}


sealed abstract class ConcRope[+T] extends Conc[T]


object ConcRope {
  import Conc._

  case class Append[+T](left: Conc[T], right: Conc[T]) extends ConcRope[T] {
    val level = 1 + math.max(left.level, right.level)
    val size = left.size + right.size
    override def normalized = wrapAppend(this, Conc.Empty)
  }

  @tailrec
  def wrapAppend[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    (xs: @unchecked) match {
      case Append(ws, zs) => wrapAppend(ws, zs <> ys)
      case xs => xs <> ys
    }
  }

  def append[T](xs: Conc[T], ys: Leaf[T]): Conc[T] = (xs: @unchecked) match {
    case xs: Append[T] => appendRec(xs, ys)
    case _ <> _ => new Append(xs, ys)
    case Empty => ys
    case xs: Leaf[T] => new <>(xs, ys)
    case xs: Prepend[T] => append(xs.normalized, ys)
  }

  @tailrec
  private def appendRec[T](xs: Append[T], ys: Conc[T]): Conc[T] = {
    if (xs.right.level > ys.level) new Append(xs, ys)
    else {
      val zs = new <>(xs.right, ys)
      xs.left match {
        case ws @ Append(_, _) => appendRec(ws, zs)
        case ws if ws.level <= zs.level => ws <> zs // note: probably can be just new <>
        case ws => new Append(ws, zs)
      }
    }
  }

  case class Prepend[+T](left: Conc[T], right: Conc[T]) extends ConcRope[T] {
    val level = 1 + math.max(left.level, right.level)
    val size = left.size + right.size
    override def normalized = wrapPrepend(Conc.Empty, this)
  }

  @tailrec
  def wrapPrepend[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    (ys: @unchecked) match {
      case Prepend(zs, ws) => wrapPrepend(xs <> zs, ws)
      case ys => xs <> ys
    }
  }

  def unprependDirect[T](xs: Conc[T]): Conc[T] = {
    def unwind(left: Conc[T], acc: Conc[T]): Conc[T] = {
      (left: @unchecked) match {
        case zs: Single[T] =>
          acc
        case zs: Chunk[T] =>
          if (zs.size > 1) {
            val nxs = Prepend(new Chunk(zs.array.tail, zs.size - 1, zs.k), acc)
            nxs
          } else {
            acc
          }
        case zs: <>[T] =>
          val left <> right = ConcUtils.shakeRight(zs)
          unwind(left, Prepend(right, acc))
      }
    }
    (xs: @unchecked) match {
      case Prepend(zs, ws) =>
        unwind(zs, ws)
      case xs: <>[T] =>
        val left <> acc = ConcUtils.shakeRight(xs)
        unwind(left, acc)
      case Empty =>
        throw new UnsupportedOperationException("Cannot unprepend on Empty.")
      case xs: Single[T] =>
        Empty
      case xs: Chunk[T] =>
        if (xs.size > 1) {
          val nxs = new Chunk(xs.array.tail, xs.size - 1, xs.k)
          nxs
        } else {
          Empty
        }
      case xs: Append[T] =>
        unprependDirect(xs.normalized)
    }
  }

  def unprepend[T](xs: Conc[T]): (T, Conc[T]) = {
    def unwind(left: Conc[T], acc: Conc[T]): (T, Conc[T]) = {
      (left: @unchecked) match {
        case zs: Single[T] =>
          (zs.x, acc)
        case zs: Chunk[T] =>
          if (zs.size > 1) {
            val nxs = Prepend(new Chunk(zs.array.tail, zs.size - 1, zs.k), acc)
            (zs.array(0), nxs)
          } else {
            (zs.array(0), acc)
          }
        case zs: <>[T] =>
          val left <> right = ConcUtils.shakeRight(zs)
          unwind(left, Prepend(right, acc))
      }
    }
    (xs: @unchecked) match {
      case Prepend(zs, ws) =>
        unwind(zs, ws)
      case xs: <>[T] =>
        val left <> acc = ConcUtils.shakeRight(xs)
        unwind(left, acc)
      case Empty =>
        throw new UnsupportedOperationException("Cannot unprepend on Empty.")
      case xs: Single[T] =>
        (xs.x, Empty)
      case xs: Chunk[T] =>
        if (xs.size > 1) {
          val nxs = new Chunk(xs.array.tail, xs.size - 1, xs.k)
          (xs.array(0), nxs)
        } else {
          (xs.array(0), Empty)
        }
      case xs: Append[T] =>
        unprepend(xs.normalized)
    }
  }

  private def isNormalized[T](xs: Conc[T]): Boolean = (xs: @unchecked) match {
    case left <> right => isNormalized(left) && isNormalized(right)
    case xs: Leaf[T] => true
    case _ => false
  }

  @tailrec
  private def isAppendList[T](xs: Conc[T]): Boolean = (xs: @unchecked) match {
    case Prepend(_, _) =>
      false
    case Append(zs @ Append(_, ws), ys) =>
      ys.level < ws.level && isNormalized(ys) && isAppendList(zs)
    case Append(zs, ys) =>
      ys.level < zs.level && isNormalized(ys) && isNormalized(zs)
  }

  @tailrec
  private def isPrependList[T](xs: Conc[T]): Boolean = (xs: @unchecked) match {
    case Append(_, _) =>
      false
    case Prepend(ys, zs @ Prepend(ws, _)) =>
      ys.level < ws.level && isNormalized(ys) && isPrependList(zs)
    case Prepend(ys, zs) =>
      ys.level < zs.level && isNormalized(ys) && isNormalized(zs)
  }

  def invariant[T](xs: Conc[T]) = (xs: @unchecked) match {
    case Append(_, _) => isAppendList(xs)
    case Prepend(_, _) => isPrependList(xs)
    case _ => isNormalized(xs)
  }

}


sealed abstract class Conqueue[+T] extends Conc[T] {
  def evaluated: Boolean
  def rear: Conqueue[T]
  def addIfUnevaluated[U >: T](stack: List[Conqueue.Spine[U]]) = stack
}


object Conqueue {

  def empty[T]: Conqueue[T] = Tip(Zero)

  case class Lazy[+T](
    lstack: List[Spine[T]], queue: Conqueue[T], rstack: List[Spine[T]]
  ) extends Conqueue[T] {
    def left = queue.left
    def right = queue.right
    def level = queue.level
    def size = queue.size
    def evaluated = unsupported("Undefined for lazy conqueue.")
    def rear = unsupported("Undefined for lazy conqueue.")
    override def normalized = queue.normalized
  }

  class Spine[+T](
    val lwing: Num[T], val rwing: Num[T], @volatile var evaluateTail: AnyRef
  ) extends Conqueue[T] {
    lazy val rear: Conqueue[T] = {
      val t = (evaluateTail: @unchecked) match {
        case eager: Conqueue[T] => eager
        case suspension: Function0[_] => suspension().asInstanceOf[Conqueue[T]]
      }
      evaluateTail = null
      t
    }
    def evaluated = evaluateTail == null
    override def addIfUnevaluated[U >: T](stack: List[Conqueue.Spine[U]]) =
      if (!evaluated) this :: stack else stack
    def left = lwing
    def right = new <>(rear, rwing)
    lazy val level: Int = 1 + math.max(lwing.level, math.max(rear.level, rwing.level))
    lazy val size: Int = lwing.size + rear.size + rwing.size
    override def normalized =
      ConcUtils.normalizeLeftWingsAndTip(
        this, Conc.Empty) <> ConcUtils.normalizeRightWings(this, Conc.Empty)
  }

  object Spine {
    def withSameTail[T](s: Spine[T], lwing: Num[T], rwing: Num[T]): Spine[T] = {
      var tail = s.evaluateTail
      if (tail eq null) tail = s.rear
      new Spine(lwing, rwing, tail)
    }
  }

  case class Tip[+T](tip: Num[T]) extends Conqueue[T] {
    def left = tip.left
    def right = tip.right
    def level = tip.level
    def size = tip.size
    def evaluated = true
    def rear = unsupported("Undefined for the tip.")
    override def normalized = tip.normalized
  }

  sealed abstract class Num[+T] extends Conc[T] {
    def leftmost: Conc[T]
    def rightmost: Conc[T]
    def digit: Int
  }

  case object Zero extends Num[Nothing] {
    def left = unsupported("Zero does not have children.")
    def right = unsupported("Zero does not have children.")
    def leftmost = unsupported("empty")
    def rightmost = unsupported("empty")
    def level: Int = 0
    def size: Int = 0
    def digit = 0
    override def normalized = Conc.Empty
  }

  case class One[+T](_1: Conc[T]) extends Num[T] {
    def left = _1
    def right = Conc.Empty
    def leftmost = _1
    def rightmost = _1
    def level: Int = 1 + _1.level
    def size: Int = _1.size
    def digit = 1
    override def normalized = _1
  }

  case class Two[+T](_1: Conc[T], _2: Conc[T]) extends Num[T] {
    def left = _1
    def right = _2
    def leftmost = _1
    def rightmost = _2
    def level: Int = 1 + math.max(_1.level, _2.level)
    def size: Int = _1.size + _2.size
    def digit = 2
    override def normalized = _1 <> _2
  }

  case class Three[+T](_1: Conc[T], _2: Conc[T], _3: Conc[T]) extends Num[T] {
    def left = _1
    def right = new <>(_2, _3)
    def leftmost = _1
    def rightmost = _3
    def level: Int = 1 + math.max(math.max(_1.level, _2.level), _3.level)
    def size: Int = _1.size + _2.size + _3.size
    def digit = 3
    override def normalized = _1 <> _2 <> _3
  }

  case class Four[+T](_1: Conc[T], _2: Conc[T], _3: Conc[T], _4: Conc[T])
  extends Num[T] {
    def left = new <>(_1, _2)
    def right = new <>(_3, _4)
    def leftmost = _1
    def rightmost = _4
    def level: Int =
      1 + math.max(math.max(_1.level, _2.level), math.max(_3.level, _4.level))
    def size: Int = _1.size + _2.size + _3.size + _4.size
    def digit = 4
    override def normalized = _1 <> _2 <> _3 <> _4
  }
}


object ConcUtils {

  import Conc._
  import ConcRope._
  import Conqueue._

  private[common] def toSeq[T](xs: Conc[T]): Seq[T] = {
    val buffer = collection.mutable.Buffer[T]()
    for (x <- xs) {
      buffer += x
    }
    buffer
  }

  def levelFormatter[T](num: Num[T]): String = num match {
    case Zero => "Zero"
    case One(_1) if _1.level == 0 || (_1.left.level == _1.right.level) =>
      s"One*(${_1.level})"
    case One(_1) => s"One(${_1.level})"
    case Two(_1, _2) => s"Two(${_1.level}, ${_2.level})"
    case Three(_1, _2, _3) => s"Three(${_1.level}, ${_2.level}, ${_3.level})"
    case Four(_1, _2, _3, _4) =>
      s"Four(${_1.level}, ${_2.level}, ${_3.level}, ${_4.level})"
  }

  private def mkstr[T](c: Conc[T]) = toSeq(c).mkString(s"l${c.level}:[", ", ", "]")

  def contentsFormatter[T](num: Num[T]): String = num match {
    case Zero => s"Zero"
    case One(_1) => s"One(${mkstr(_1)})"
    case Two(_1, _2) => s"Two(${mkstr(_1)}, ${mkstr(_2)})"
    case Three(_1, _2, _3) => s"Three(${mkstr(_1)}, ${mkstr(_2)}, ${mkstr(_3)}})"
    case Four(_, _, _, _) => invalid("never four.")
  }

  private def mkstrn[T](c: Conc[Conc[T]]) = toSeq(c).map(mkstr).mkString("[", ", ", "]")

  def nestedContentsFormatter[T](num: Num[Conc[T]]): String = num match {
    case Zero => s"Zero"
    case One(_1) => s"One(${mkstrn(_1)})"
    case Two(_1, _2) => s"Two(${mkstrn(_1)}, ${mkstrn(_2)})"
    case Three(_1, _2, _3) => s"Three(${mkstrn(_1)}, ${mkstrn(_2)}, ${mkstrn(_3)}})"
    case Four(_, _, _, _) => invalid("never four.")
  }

  def queueString[T](
    conq: Conqueue[T], showNum: Num[T] => String = levelFormatter _, spacing: Int = 80
  ): String = {
    val buffer = new StringBuffer

    def traverse(
      rank: Int, indent: Int, conq: Conqueue[T]
    ): Unit = (conq: @unchecked) match {
      case s: Spine[T] =>
        val lefts = showNum(s.lwing)
        val rights = showNum(s.rwing)
        val spines = "Spine(+)"
        buffer.append(
          " " * (indent - lefts.length) + lefts + " " + spines + " " + rights)
        buffer.append("\n")
        traverse(rank + 1, indent, s.rear)
      case Tip(tip) =>
        val tips = s"Tip(${showNum(tip)})"
        buffer.append(" " * (indent) + tips)
      case Lazy(_, conq, _) =>
        buffer.append(" " * (indent) + "Lazy(+)")
        buffer.append("\n")
        traverse(rank, indent, conq)
    }

    traverse(0, spacing, conq)
    buffer.toString
  }

  def foreach[
    @specialized(Int, Long, Float, Double) T,
    @specialized(Int, Long, Float, Double) U
  ](xs: Conc[T], f: T => U): Unit = (xs: @unchecked) match {
    case left <> right =>
      foreach(left, f)
      foreach(right, f)
    case s: Single[T] =>
      f(s.x)
    case c: Chunk[T] =>
      val a = c.array
      val sz = c.size
      var i = 0
      while (i < sz) {
        f(a(i))
        i += 1
      }
    case Empty =>
    case Append(left, right) =>
      foreach(left, f)
      foreach(right, f)
    case Prepend(left, right) =>
      foreach(left, f)
      foreach(right, f)
    case Zero =>
    case One(_1) =>
      foreach(_1, f)
    case Two(_1, _2) =>
      foreach(_1, f)
      foreach(_2, f)
    case Three(_1, _2, _3) =>
      foreach(_1, f)
      foreach(_2, f)
      foreach(_3, f) 
    case Tip(Zero) =>
    case Tip(num) =>
      foreach(num, f)
    case Lazy(_, conq, _) =>
      foreach(conq, f)
    case st: Spine[T] =>
      foreach(st.lwing, f)
      foreach(st.rear, f)
      foreach(st.rwing, f)
    case _ =>
      invalid("All cases should have been covered: " + xs + ", " + xs.getClass)
  }

  def foreachLeafLeft[T](xs: Conc[T])(
    f: Leaf[T] => Unit
  ): Unit = (xs: @unchecked) match {
    case left <> right =>
      foreachLeafLeft(left)(f)
      foreachLeafLeft(right)(f)
    case Empty =>
    case leaf: Leaf[T] =>
      f(leaf)
    case Append(left, right) =>
      // TODO: investigate if this case is necessary here.
      foreachLeafLeft(left)(f)
      foreachLeafLeft(right)(f)
    case Zero =>
    case One(_1) =>
      foreachLeafLeft(_1)(f)
    case Two(_1, _2) =>
      foreachLeafLeft(_1)(f)
      foreachLeafLeft(_2)(f)
    case Three(_1, _2, _3) =>
      foreachLeafLeft(_1)(f)
      foreachLeafLeft(_2)(f)
      foreachLeafLeft(_3)(f) 
    case Tip(Zero) =>
    case Tip(num) =>
      foreachLeafLeft(num)(f)
    case Lazy(_, conq, _) =>
      foreachLeafLeft(conq)(f)
    case st: Spine[T] =>
      foreachLeafLeft(st.lwing)(f)
      foreachLeafLeft(st.rear)(f)
      foreachLeafLeft(st.rwing)(f)
    case _ =>
      invalid("All cases should have been covered: " + xs + ", " + xs.getClass)
  }

  def foreachLeafRight[T](xs: Conc[T])(
    f: Leaf[T] => Unit
  ): Unit = (xs: @unchecked) match {
    case left <> right =>
      foreachLeafRight(right)(f)
      foreachLeafRight(left)(f)
    case Empty =>
    case leaf: Leaf[T] =>
      f(leaf)
    case Append(left, right) =>
      // TODO: investigate if this case is necessary here.
      foreachLeafRight(right)(f)
      foreachLeafRight(left)(f)
    case Zero =>
    case One(_1) =>
      foreachLeafRight(_1)(f)
    case Two(_1, _2) =>
      foreachLeafRight(_2)(f)
      foreachLeafRight(_1)(f)
    case Three(_1, _2, _3) =>
      foreachLeafRight(_3)(f) 
      foreachLeafRight(_2)(f)
      foreachLeafRight(_1)(f)
    case Tip(Zero) =>
    case Tip(num) =>
      foreachLeafRight(num)(f)
    case Lazy(_, conq, _) =>
      foreachLeafRight(conq)(f)
    case st: Spine[T] =>
      foreachLeafRight(st.rwing)(f)
      foreachLeafRight(st.rear)(f)
      foreachLeafRight(st.lwing)(f)
    case _ =>
      invalid("All cases should have been covered: " + xs + ", " + xs.getClass)
  }

  def apply[@specialized(Int, Long, Float, Double) T](
    xs: Conc[T], i: Int
  ): T = (xs: @unchecked) match {
    case left <> _ if i < left.size =>
      apply(left, i)
    case left <> right =>
      apply(right, i - left.size)
    case st: Spine[T] =>
      if (i < st.lwing.size) apply(st.lwing, i)
      else if (i < st.lwing.size + st.rear.size) apply(st.rear, i - st.lwing.size)
      else apply(st.rwing, i - st.lwing.size - st.rear.size)
    case s: Single[T] => s.x
    case c: Chunk[T] => c.array(i)
    case Append(left, _) if i < left.size =>
      apply(left, i)
    case Append(left, right) =>
      apply(right, i - left.size)
    case Prepend(left, right) if i < left.size =>
      apply(left, i)
    case Prepend(left, right) =>
      apply(right, i - left.size)
    case One(_1) =>
      apply(_1, i)
    case Two(_1, _2) =>
      if (i < _1.size) apply(_1, i)
      else apply(_2, i - _1.size)
    case Three(_1, _2, _3) =>
      if (i < _1.size) apply(_1, i)
      else if (i < _1.size + _2.size) apply(_2, i - _1.size)
      else apply(_3, i - _1.size - _2.size)
    case Tip(num) =>
      apply(num, i)
    case Lazy(_, conq, _) =>
      apply(conq, i)
  }

  private def updatedArray[
    @specialized(Int, Long, Float, Double) T: ClassTag
  ](a: Array[T], i: Int, y: T, sz: Int): Array[T] = {
    val na = new Array[T](a.length)
    System.arraycopy(a, 0, na, 0, sz)
    na(i) = y
    na
  }

  def asConqueue[T](xs: Conc[T]) = xs.asInstanceOf[Conqueue[T]]

  def asNum[T](xs: Conc[T]) = xs.asInstanceOf[Num[T]]

  def update[
    @specialized(Int, Long, Float, Double) T: ClassTag
  ](xs: Conc[T], i: Int, y: T): Conc[T] = (xs: @unchecked) match {
    case left <> right if i < left.size =>
      new <>(update(left, i, y), right)
    case left <> right =>
      val ni = i - left.size
      new <>(left, update(right, ni, y))
    case s: Single[T] =>
      new Single(y)
    case c: Chunk[T] =>
      new Chunk(updatedArray(c.array, i, y, c.size), c.size, c.k)
    case Append(left, right) if i < left.size => // TODO: see if this should be removed.
      new Append(update(left, i, y), right)
    case Append(left, right) =>
      new Append(left, update(right, i - left.size, y))
    case st: Spine[T] =>
      if (i < st.lwing.size) {
        val nlwing = asNum(update(st.lwing, i, y))
        Spine.withSameTail(st, nlwing, st.rwing)
      } else {
        val lwingrearsize = st.lwing.size + st.rear.size
        if (i >= lwingrearsize) {
          val nrwing = asNum(update(st.rwing, i - lwingrearsize, y))
          new Spine(st.lwing, nrwing, st.rear)
        } else {
          val nrear = asConqueue(update(st.rear, i - st.lwing.size, y))
          new Spine(st.lwing, st.rwing, nrear)
        }
      }
    case Tip(n) =>
      Tip(asNum(update(n, i, y)))
    case One(_1) =>
      One(update(_1, i, y))
    case Two(_1, _2) =>
      if (i < _1.size) Two(update(_1, i, y), _2)
      else Two(_1, update(_2, i - _1.size, y))
    case Three(_1, _2, _3) =>
      if (i < _1.size) Three(update(_1, i, y), _2, _3)
      else if (i < _1.size + _2.size) Three(_1, update(_2, i - _1.size, y), _3)
      else Three(_1, _2, update(_3, i - _1.size - _2.size, y))
    case _ =>
      invalid("All cases should have been covered: " + xs + ", " + xs.getClass)
  }

  def concatConqueueTop[T](xs: Conqueue[T], ys: Conqueue[T]): Conqueue[T] = {
    if (xs.level < 32 && (1 << xs.level) <= ys.level) {
      var nys = ys
      foreachLeafRight(xs)(leaf => nys = pushHeadTop(nys, leaf))
      nys
    } else if (ys.level < 32 && (1 << ys.level) <= xs.level) {
      var nxs = xs
      foreachLeafLeft(ys)(leaf => nxs = pushLastTop(nxs,leaf))
      nxs
    } else {
      toConqueue(concat(xs.normalized, ys.normalized))
    }
  }

  def concat[T](xs: Conc[T], ys: Conc[T]) = {
    if (xs == Empty) ys
    else if (ys == Empty) xs
    else concatRec(xs, ys)
  }

  private def concatRec[T](xs: Conc[T], ys: Conc[T]): Conc[T] = {
    val diff = ys.level - xs.level
    if (diff >= -1 && diff <= 1) new <>(xs, ys)
    else if (diff < -1) {
      if (xs.left.level >= xs.right.level) {
        val nr = concatRec(xs.right, ys)
        new <>(xs.left, nr)
      } else {
        val nrr = concatRec(xs.right.right, ys)
        if (nrr.level == xs.level - 3) {
          val nl = xs.left
          val nr = new <>(xs.right.left, nrr)
          new <>(nl, nr)
        } else {
          val nl = new <>(xs.left, xs.right.left)
          val nr = nrr
          new <>(nl, nr)
        }
      }
    } else {
      if (ys.right.level >= ys.left.level) {
        val nl = concatRec(xs, ys.left)
        new <>(nl, ys.right)
      } else {
        val nll = concatRec(xs, ys.left.left)
        if (nll.level == ys.level - 3) {
          val nl = new <>(nll, ys.left.right)
          val nr = ys.right
          new <>(nl, nr)
        } else {
          val nl = nll
          val nr = new <>(ys.left.right, ys.right)
          new <>(nl, nr)
        }
      }
    }
  }

  private[common] def insertedArray[
    @specialized(Int, Long, Float, Double) T: ClassTag
  ](a: Array[T], from: Int, i: Int, y: T, sz: Int): Array[T] = {
    val na = new Array[T](sz + 1)
    System.arraycopy(a, from, na, 0, i)
    na(i) = y
    System.arraycopy(a, from + i, na, i + 1, sz - i)
    na
  }

  private[common] def removedArray[T: ClassTag](
    a: Array[T], from: Int, at: Int, sz: Int
  ): Array[T] = {
    val na = new Array[T](sz - 1)
    System.arraycopy(a, from, na, 0, at)
    System.arraycopy(a, from + at + 1, na, at, sz - at - 1)
    na
  }

  private[common] def copiedArray[T: ClassTag](
    a: Array[T], from: Int, sz: Int
  ): Array[T] = {
    val na = new Array[T](sz)
    System.arraycopy(a, from, na, 0, sz)
    na
  }

  def insert[@specialized(Int, Long, Float, Double) T: ClassTag](
    xs: Conc[T], i: Int, y: T
  ): Conc[T] = (xs.normalized: @unchecked) match {
    case left <> right if i < left.size =>
      insert(left, i, y) <> right
    case left <> right =>
      left <> insert(right, i - left.size, y)
    case s: Single[T] =>
      if (i == 0) new <>(new Single(y), xs)
      else new <>(xs, new Single(y))
    case c: Chunk[T] if c.size == c.k =>
      val a = c.array
      val sz = c.size
      val k = c.k
      if (i < k / 2) {
        val la = insertedArray(a, 0, i, y, k / 2)
        val ra = copiedArray(a, k / 2, k - k / 2)
        new <>(new Chunk(la, k / 2 + 1, k), new Chunk(ra, k - k / 2, k))
      } else {
        val la = copiedArray(a, 0, k / 2)
        val ra = insertedArray(a, k / 2, i - k / 2, y, k - k / 2 + 1)
        new <>(new Chunk(la, k / 2, k), new Chunk(ra, k - k / 2 + 1, k))
      }
    case c: Chunk[T] =>
      val a = c.array
      val sz = c.size
      val k = c.k
      new Chunk(insertedArray(a, 0, i, y, sz), sz + 1, k)
    case Empty =>
      new Single(y)
    case _ =>
      invalid("undefined for conqueues.")
  }

  def shakeLeft[T](xs: Conc[T]): Conc[T] = {
    if (xs.level <= 1) {
      //
      //       1       
      //    +--+--+    
      //    0     0    
      //
      xs
    } else if (xs.left.level >= xs.right.level) {
      //
      //                 n             
      //           +-----+-----+       
      //         n - 1       n - 1     
      //       +---+---+    (n - 2)    
      //     n - 2   n - 2             
      //    (n - 3) (n - 2)            
      //    (n - 2) (n - 3)            
      //
      xs
    } else if (xs.right.right.level >= xs.right.left.level) {
      //
      //            n                              n         
      //      +-----+-----+                  +-----+-----+   
      //    n - 2       n - 1      =>      n - 1       n - 2 
      //              +---+---+          +---+---+    (n - 2)
      //            n - 2   n - 2      n - 2   n - 2         
      //           (n - 3) (n - 2)            (n - 3)        
      //
      val nl = new <>(xs.left, xs.right.left)
      val nr = xs.right.right
      new <>(nl, nr)
    } else if (xs.left.left.level >= xs.left.right.level) {
      //
      //                    n                                      n                
      //          +---------+---------+                  +---------+---------+      
      //        n - 2               n - 1      =>      n - 1               n - 2    
      //      +---+---+           +---+---+          +---+---+           +---+---+  
      //    n - 3   n - 3       n - 2   n - 3      n - 3   n - 2       n - 3   n - 3
      //                      +---+---+                  +---+---+    (n - 4)       
      //                    n - 3   n - 3              n - 3   n - 3  (n - 3)       
      //                   (n - 3) (n - 4)                    (n - 3)               
      //                   (n - 4) (n - 3)                    (n - 4)               
      //
      //  OR:
      //
      //                    n                                      n                
      //          +---------+---------+                  +---------+---------+      
      //        n - 2               n - 1      =>      n - 1               n - 2    
      //      +---+---+           +---+---+          +---+---+           +---+---+  
      //    n - 3   n - 4       n - 2   n - 3      n - 3   n - 2       n - 3   n - 3
      //                      +---+---+                  +---+---+    (n - 4)       
      //                    n - 3   n - 3              n - 4   n - 3                
      //                   (n - 3) (n - 4)                    (n - 3)               
      //
      //  OR:
      //
      //                    n                                    n - 1              
      //          +---------+---------+                  +---------+---------+      
      //        n - 2               n - 1      =>      n - 2               n - 2    
      //      +---+---+           +---+---+          +---+---+           +---+---+  
      //    n - 3   n - 4       n - 2   n - 3      n - 3   n - 3       n - 3   n - 3
      //                      +---+---+                  +---+---+                  
      //                    n - 4   n - 3              n - 4   n - 4                
      //
      val nll = xs.left.left
      val nlr = new <>(xs.left.right, xs.right.left.left)
      val nl = new <>(nll, nlr)
      val nr = new <>(xs.right.left.right, xs.right.right)
      new <>(nl, nr)
    } else if (xs.right.left.left.level >= xs.right.left.right.level) {
      //
      //                    n                    
      //          +---------+---------+          
      //        n - 2               n - 1      =>
      //      +---+---+           +---+---+      
      //    n - 4   n - 3       n - 2   n - 3    
      //                      +---+---+          
      //                    n - 3   n - 3        
      //                   (n - 3) (n - 4)       
      //
      //                           n                
      //                 +---------+---------+      
      //               n - 1               n - 2    
      //          +------+------+        +---+---+  
      //        n - 2         n - 3    n - 3   n - 3
      //      +---+---+      (n - 3)  (n - 4)       
      //    n - 4   n - 3                           
      //
      val nl = new <>(xs.left, xs.right.left.left)
      val nr = new <>(xs.right.left.right, xs.right.right)
      new <>(nl, nr)
    } else {
      //
      //                       n                       
      //          +------------+------------+          
      //        n - 2                     n - 1      =>
      //      +---+---+                 +---+---+      
      //    n - 4   n - 3             n - 2   n - 3    
      //          +---+---+         +---+---+          
      //        n - 4   n - 4     n - 4   n - 3        
      //       (n - 4) (n - 5)                         
      //       (n - 5) (n - 4)                         
      //
      //                             n - 1                 
      //                  +------------+------------+      
      //                n - 2                     n - 2    
      //        +---------+---------+           +---+---+  
      //      n - 3               n - 3       n - 3   n - 3
      //    +---+---+           +---+---+                  
      //  n - 4   n - 4       n - 4   n - 4                
      //         (n - 4)     (n - 5)                       
      //         (n - 5)     (n - 4)                       
      //
      val nll = new <>(xs.left.left, xs.left.right.left)
      val nlr = new <>(xs.left.right.right, xs.right.left.left)
      val nl = new <>(nll, nlr)
      val nr = new <>(xs.right.left.right, xs.right.right)
      new <>(nl, nr)
    }
  }

  def shakeRight[T](xs: Conc[T]): Conc[T] = {
    if (xs.level <= 1) {
      //
      //       1       
      //    +--+--+    
      //    0     0    
      //
      xs
    } else if (xs.left.level <= xs.right.level) {
      //
      //             n                 
      //       +-----+-----+           
      //     n - 1       n - 1         
      //    (n - 2)    +---+---+       
      //             n - 2   n - 2     
      //            (n - 3) (n - 2)    
      //            (n - 2) (n - 3)    
      //
      xs
    } else if (xs.left.left.level >= xs.left.right.level) {
      //
      //                 n                      n            
      //           +-----+-----+          +-----+-----+      
      //         n - 1       n - 2  =>  n - 2       n - 1    
      //       +---+---+               (n - 2)    +---+---+  
      //     n - 2   n - 2                      n - 2   n - 2
      //    (n - 2) (n - 3)                    (n - 3)       
      //
      val nl = xs.left.left
      val nr = new <>(xs.left.right, xs.right)
      new <>(nl, nr)
    } else if (xs.right.right.level >= xs.right.left.level) {
      //
      //                    n                                      n                
      //          +---------+---------+                  +---------+---------+      
      //        n - 1               n - 2      =>      n - 2               n - 1    
      //      +---+---+           +---+---+          +---+---+           +---+---+  
      //    n - 3   n - 2       n - 3   n - 3      n - 3   n - 3       n - 2   n - 3
      //          +---+---+                               (n - 4)    +---+---+      
      //        n - 3   n - 3                             (n - 3)  n - 3   n - 3    
      //       (n - 4) (n - 3)                                    (n - 3)           
      //       (n - 3) (n - 4)                                    (n - 4)           
      //
      //  OR:
      //
      //                    n                                      n                
      //          +---------+---------+                  +---------+---------+      
      //        n - 1               n - 2      =>      n - 2               n - 1    
      //      +---+---+           +---+---+          +---+---+           +---+---+  
      //    n - 3   n - 2       n - 4   n - 3      n - 3   n - 3       n - 2   n - 3
      //          +---+---+                               (n - 4)    +---+---+      
      //        n - 3   n - 3                                      n - 3   n - 4    
      //       (n - 4) (n - 3)                                    (n - 3)           
      //
      //  OR:
      //
      //                    n                                    n - 1              
      //          +---------+---------+                  +---------+---------+      
      //        n - 1               n - 2      =>      n - 2               n - 2    
      //      +---+---+           +---+---+          +---+---+           +---+---+  
      //    n - 3   n - 2       n - 4   n - 3      n - 3   n - 3       n - 3   n - 3
      //          +---+---+                                          +---+---+      
      //        n - 3   n - 4                                      n - 4   n - 4    
      //
      val nl = new <>(xs.left.left, xs.left.right.left)
      val nrl = new <>(xs.left.right.right, xs.right.left)
      val nrr = xs.right.right
      val nr = new <>(nrl, nrr)
      new <>(nl, nr)
    } else if (xs.left.right.right.level >= xs.left.right.left.level) {
      //
      //                    n                    
      //          +---------+---------+          
      //        n - 1               n - 2      =>
      //      +---+---+           +---+---+      
      //    n - 3   n - 2       n - 3   n - 4    
      //          +---+---+                      
      //        n - 3   n - 3                    
      //       (n - 4) (n - 3)                   
      //
      //                  n                       
      //        +---------+---------+             
      //      n - 2               n - 1           
      //    +---+---+        +------+------+      
      //  n - 3   n - 3    n - 3         n - 2    
      //         (n - 4)  (n - 3)      +---+---+  
      //                             n - 3   n - 4
      //                                          
      //
      val nl = new <>(xs.left.left, xs.left.right.left)
      val nr = new <>(xs.left.right.right, xs.right)
      new <>(nl, nr)
    } else {
      //
      //                       n                       
      //          +------------+------------+          
      //        n - 1                     n - 2      =>
      //      +---+---+                 +---+---+      
      //    n - 3   n - 2             n - 3   n - 4    
      //          +---+---+         +---+---+          
      //        n - 3   n - 4     n - 4   n - 4        
      //                         (n - 5) (n - 4)       
      //                         (n - 4) (n - 5)       
      //
      //                   n - 1                           
      //        +------------+------------+                
      //      n - 2                     n - 2              
      //    +---+---+           +---------+---------+      
      //  n - 3   n - 3       n - 3               n - 3    
      //                    +---+---+           +---+---+  
      //                  n - 4   n - 4       n - 4   n - 4
      //                         (n - 5)     (n - 4)       
      //                         (n - 4)     (n - 5)       
      //
      val nl = new <>(xs.left.left, xs.left.right.left)
      val nrl = new <>(xs.left.right.right, xs.right.left.left)
      val nrr = new <>(xs.right.left.right, xs.right.right)
      val nr = new <>(nrl, nrr)
      new <>(nl, nr)
    }
  }

  def pay[T](work: List[Spine[T]], n: Int): List[Spine[T]] =
    if (n == 0) work else work match {
      case head :: rest =>
        // do 2 units of work
        val tail = head.rear
        pay(tail.addIfUnevaluated(rest), n - 1)
      case Nil =>
        // hoorah - nothing to do
        Nil
    }

  val doNothing = () => {}

  def noCarryPushHead[T](num: Num[T], c: Conc[T]): Num[T] =
    (num.digit: @switch) match {
      case 0 =>
        One(c)
      case 1 =>
        val One(_1) = num
        Two(c, _1)
      case 2 =>
        val Two(_1, _2) = num
        Three(c, _1, _2)
      case _ =>
        invalid("Causes a carry.")
    }

  def noCarryPushLast[T](num: Num[T], c: Conc[T]): Num[T] =
    (num.digit: @switch) match {
      case 0 =>
        One(c)
      case 1 =>
        val One(_1) = num
        Two(_1, c)
      case 2 =>
        val Two(_1, _2) = num
        Three(_1, _2, c)
      case _ =>
        invalid("Causes a carry.")
    }

  def noCarryAdd[T](n: Num[T], m: Num[T]): Num[T] = (n.digit: @switch) match {
    case 0 =>
      m
    case 1 =>
      val One(n1) = n
      (m.digit: @switch) match {
        case 0 =>
          n
        case 1 =>
          val One(m1) = m
          Two(n1, m1)
        case 2 =>
          val Two(m1, m2) = m
          Three(n1, m1, m2)
        case 3 =>
          val Three(m1, m2, m3) = m
          Four(n1, m1, m2, m3)
        case _ =>
          invalid("Causes a carry.")
      }
    case 2 =>
      val Two(n1, n2) = n
      (m.digit: @switch) match {
        case 0 =>
          n
        case 1 =>
          val One(m1) = m
          Three(n1, n2, m1)
        case 2 =>
          val Two(m1, m2) = m
          Four(n1, n2, m1, m2)
        case _ =>
          invalid("Causes a carry.")
      }
    case 3 =>
      val Three(n1, n2, n3) = n
      (m.digit: @switch) match {
        case 0 =>
          n
        case 1 =>
          val One(m1) = m
          Four(n1, n2, n3, m1)
        case _ =>
          invalid("Causes a carry.")
      }
    case 4 =>
      (m.digit: @switch) match {
        case 0 =>
          n
        case _ =>
          invalid("Causes a carry.")
      }
  }

  def noBorrowPopHead[T](num: Num[T]): Num[T] = (num.digit: @switch) match {
    case 0 =>
      unsupported("empty")
    case 1 =>
      Zero
    case 2 =>
      val Two(_1, _2) = num
      One(_2)
    case 3 =>
      val Three(_1, _2, _3) = num
      Two(_2, _3)
    case 4 =>
      invalid("Four should never happen.")
  }

  def noBorrowPopLast[T](num: Num[T]): Num[T] = (num.digit: @switch) match {
    case 0 =>
      unsupported("empty")
    case 1 =>
      Zero
    case 2 =>
      val Two(_1, _2) = num
      One(_1)
    case 3 =>
      val Three(_1, _2, _3) = num
      Two(_1, _2)
    case 4 =>
      invalid("Four should never happen.")
  }

  def pushHead[T](
    conq: Conqueue[T], c: Conc[T], onPush: () => Unit = doNothing
  ): Conqueue[T] = {
    onPush()

    (conq: @unchecked) match {
      case s: Spine[T] =>
        if (s.lwing.digit < 3) {
          Spine.withSameTail(s, noCarryPushHead(s.lwing, c), s.rwing)
        } else {
          val Three(_1, _2, _3) = s.lwing
          val nlwing = Two(c, _1)
          val carry = _2 <> _3
          val ntail = (s.rear: @unchecked) match {
            case st: Spine[T] if st.lwing.digit == 3 =>
              () => pushHead(s.rear, carry, onPush)
            case _ =>
              pushHead(s.rear, carry, onPush)
          }
          new Spine(nlwing, s.rwing, ntail)
        }
      case Tip(tip) =>
        if (tip.digit < 3) {
          Tip(noCarryPushHead(tip, c))
        } else {
          val Three(_1, _2, _3) = tip
          new Spine(Two(c, _1), Two(_2, _3), Tip(Zero))
        }
    }
  }

  def pushHeadTop[T](
    conq: Conqueue[T], leaf: Leaf[T], onPush: () => Unit = doNothing
  ): Conqueue[T] = conq match {
    case Conqueue.Lazy(lstack, queue, rstack) =>
      val nqueue = pushHead(queue, leaf, onPush)
      val nlstack = pay(nqueue.addIfUnevaluated(lstack), 2)
      val nrstack = pay(rstack, 2)
      Conqueue.Lazy(nlstack, nqueue, nrstack)
    case _ =>
      pushHead(conq, leaf, onPush)
  }

  def fixLeft[T](s: Spine[T], onFix: () => Unit = doNothing): Spine[T] = {
    def spreadBorrow(
      b: Conc[T], otail: Spine[T], nttail: Conqueue[T], continue: Boolean
    ): Spine[T] = {
      val bshaken = shakeRight(b)
      if (bshaken.level == b.level) {
        if (bshaken.left.level == b.level - 1) {
          // regular Two in position n - 1
          val ntlwing = Two(bshaken.left, bshaken.right)
          val ntspine = new Spine(ntlwing, otail.rwing, nttail)
          val ntail = if (continue) ntspine else () => fixLeft(ntspine, onFix)
          new Spine(s.lwing, s.rwing, ntail)
        } else {
          // regular One in position n - 1, regular One in position n - 2
          val ntlwing = One(bshaken.right)
          val ntspine = new Spine(ntlwing, otail.rwing, nttail)
          val ntail = if (continue) ntspine else () => fixLeft(ntspine, onFix)
          val nlwing = noCarryPushLast(s.lwing, bshaken.left)
          new Spine(nlwing, s.rwing, ntail)
        }
      } else {
        // excited One in position n - 1
        val ntlwing = One(bshaken)
        val ntspine = new Spine(ntlwing, otail.rwing, nttail)
        val ntail = if (continue) ntspine else () => fixLeft(ntspine, onFix)
        new Spine(s.lwing, s.rwing, ntail)
      }
    }

    onFix()

    (s.rear: @unchecked) match {
      case st: Spine[T] if st.lwing.digit == 0 =>
        (st.rear: @unchecked) match {
          case stt: Spine[T] =>
            val nttlwing = noBorrowPopHead(stt.lwing)
            val nttail = Spine.withSameTail(stt, nttlwing, stt.rwing)
            spreadBorrow(stt.lwing.leftmost, st, nttail, nttlwing.digit > 0)
          case Tip(Zero) =>
            new Spine(s.lwing, s.rwing, Tip(st.rwing))
          case Tip(tip) =>
            spreadBorrow(tip.leftmost, st, Tip(noBorrowPopHead(tip)), false)
        }
      case _ =>
        s
    }
  }

  def popHead[T](conq: Conqueue[T], onFix: () => Unit = doNothing): Conqueue[T] = {
    (conq: @unchecked) match {
      case s: Spine[T] =>
        if (s.lwing.digit > 1) {
          Spine.withSameTail(s, noBorrowPopHead(s.lwing), s.rwing)
        } else {
          (s.rear: @unchecked) match {
            case st: Spine[T] => // note: s is at rank 0
              val tleftmost = st.lwing.leftmost
              val nlwing = Two(tleftmost.left, tleftmost.right)
              val ntlwing = noBorrowPopHead(st.lwing)
              val ntail = Spine.withSameTail(st, ntlwing, st.rwing)
              val nspine = new Spine(nlwing, s.rwing, ntail)
              if (ntlwing.digit > 0) nspine else fixLeft(nspine, onFix)
            case Tip(Zero) =>
              Tip(s.rwing)
            case Tip(tip) =>
              val leftmost = tip.leftmost
              val nlwing = Two(leftmost.left, leftmost.right)
              val ntip = Tip(noBorrowPopHead(tip))
              new Spine(nlwing, s.rwing, ntip)
          }
        }
      case Tip(tip) =>
        Tip(noBorrowPopHead(tip))
    }
  }

  def popHeadTop[T](conq: Conqueue[T], onFix: () => Unit = doNothing): Conqueue[T] =
    conq match {
      case Conqueue.Lazy(lstack, queue, rstack) =>
        val nqueue = popHead(queue, onFix)
        val nlstack = pay(nqueue.addIfUnevaluated(lstack), 2)
        val nrstack = pay(rstack, 2)
        Conqueue.Lazy(nlstack, nqueue, nrstack)
      case _ =>
        popHead(conq, onFix)
    }

  def head[T](conq: Conqueue[T]): Leaf[T] = {
    @tailrec def leftmost(c: Conc[T]): Leaf[T] = c match {
      case Empty => invalid("Num should never have a Zero.")
      case l: Leaf[T] => l
      case _ <> _ => leftmost(c.left)
      case _ => invalid("Invalid conqueue state.")
    }

    (conq: @unchecked) match {
      case s: Spine[T] =>
        leftmost(s.lwing.leftmost)
      case Tip(Zero) =>
        null
      case Tip(tip) =>
        leftmost(tip.leftmost)
      case Lazy(_, queue, _) =>
        head(queue)
    }
  }

  def pushLast[T](
    conq: Conqueue[T], c: Conc[T], onPush: () => Unit = doNothing
  ): Conqueue[T] = {
    onPush()

    (conq: @unchecked) match {
      case s: Spine[T] =>
        if (s.rwing.digit < 3) {
          Spine.withSameTail(s, s.lwing, noCarryPushLast(s.rwing, c))
        } else {
          val Three(_1, _2, _3) = s.rwing
          val nrwing = Two(_3, c)
          val carry = _1 <> _2
          val ntail = (s.rear: @unchecked) match {
            case st: Spine[T] =>
              () => pushLast(s.rear, carry, onPush)
            case Tip(_) =>
              pushLast(s.rear, carry, onPush)
          }
          new Spine(s.lwing, nrwing, ntail)
        }
      case Tip(tip) =>
        if (tip.digit < 3) {
          Tip(noCarryPushLast(tip, c))
        } else {
          val Three(_1, _2, _3) = tip
          new Spine(Two(_1, _2), Two(_3, c), Tip(Zero))
        }
    }
  }

  def pushLastTop[T](
    conq: Conqueue[T], leaf: Leaf[T], onPush: () => Unit = doNothing
  ): Conqueue[T] = conq match {
    case Conqueue.Lazy(lstack, queue, rstack) =>
      val nqueue = pushLast(queue, leaf, onPush)
      val nlstack = pay(lstack, 2)
      val nrstack = pay(nqueue.addIfUnevaluated(rstack), 2)
      Conqueue.Lazy(nlstack, nqueue, nrstack)
    case _ =>
      pushLast(conq, leaf, onPush)
  }

  def fixRight[T](s: Spine[T], onFix: () => Unit = doNothing): Spine[T] = {
    onFix()
    def spreadBorrow(
      b: Conc[T], otail: Spine[T], nttail: Conqueue[T], continued: Boolean
    ): Spine[T] = {
      val bshaken = shakeLeft(b)
      if (bshaken.level == b.level) {
        if (bshaken.right.level == b.level - 1) {
          // regular Two in position n - 1
          val ntrwing = Two(bshaken.left, bshaken.right)
          val ntspine = new Spine(otail.lwing, ntrwing, nttail)
          val ntail = if (continued) ntspine else () => fixRight(ntspine, onFix)
          new Spine(s.lwing, s.rwing, ntail)
        } else {
          // regular One in position n - 1, regular One in position n - 2
          val ntrwing = One(bshaken.left)
          val ntspine = new Spine(otail.lwing, ntrwing, nttail)
          val ntail = if (continued) ntspine else () => fixRight(ntspine, onFix)
          val nrwing = noCarryPushHead(s.rwing, bshaken.right)
          new Spine(s.lwing, nrwing, ntail)
        }
      } else {
        // excited One in position n - 1
        val ntrwing = One(bshaken)
        val ntspine = new Spine(otail.lwing, ntrwing, nttail)
        val ntail = if (continued) ntspine else () => fixRight(ntspine, onFix)
        new Spine(s.lwing, s.rwing, ntail)
      }
    }
    (s.rear: @unchecked) match {
      case st: Spine[T] if st.rwing.digit == 0 =>
        (st.rear: @unchecked) match {
          case stt: Spine[T] =>
            val nttrwing = noBorrowPopLast(stt.rwing)
            val nttail = Spine.withSameTail(stt, stt.lwing, nttrwing)
            spreadBorrow(stt.rwing.rightmost, st, nttail, nttrwing.digit > 0)
          case Tip(Zero) =>
            new Spine(s.lwing, s.rwing, Tip(st.lwing))
          case Tip(tip) =>
            spreadBorrow(tip.rightmost, st, Tip(noBorrowPopLast(tip)), false)
        }
      case _ =>
        s
    }
  }

  def popLast[T](conq: Conqueue[T], onFix: () => Unit = doNothing): Conqueue[T] = {
    (conq: @unchecked) match {
      case s: Spine[T] =>
        if (s.rwing.digit > 1) {
          Spine.withSameTail(s, s.lwing, noBorrowPopLast(s.rwing))
        } else {
          (s.rear: @unchecked) match {
            case st: Spine[T] => // note: s is at rank 0
              val trightmost = st.rwing.rightmost
              val nrwing = Two(trightmost.left, trightmost.right)
              val ntrwing = noBorrowPopLast(st.rwing)
              val ntail = Spine.withSameTail(st, st.lwing, ntrwing)
              val nspine = new Spine(s.lwing, nrwing, ntail)
              if (ntrwing.digit > 0) nspine else fixRight(nspine, onFix)
            case Tip(Zero) =>
              Tip(s.lwing)
            case Tip(tip) =>
              val rightmost = tip.rightmost
              val nrwing = Two(rightmost.left, rightmost.right)
              val ntip = Tip(noBorrowPopLast(tip))
              new Spine(s.lwing, nrwing, ntip)
          }
        }
      case Tip(tip) =>
        Tip(noBorrowPopLast(tip))
    }
  }

  def popLastTop[T](
    conq: Conqueue[T], onFix: () => Unit = doNothing
  ): Conqueue[T] = conq match {
    case Conqueue.Lazy(lstack, queue, rstack) =>
      val nqueue = popLast(queue, onFix)
      val nlstack = pay(lstack, 2)
      val nrstack = pay(nqueue.addIfUnevaluated(rstack), 2)
      Conqueue.Lazy(nlstack, nqueue, nrstack)
    case _ =>
      popLast(conq, onFix)
  }

  def last[T](conq: Conqueue[T]): Leaf[T] = {
    @tailrec def rightmost(c: Conc[T]): Leaf[T] = c match {
      case Empty => invalid("Num should never have a Zero.")
      case l: Leaf[T] => l
      case _ <> _ => rightmost(c.right)
      case _ => invalid("Invalid conqueue state: " + c.getClass.getSimpleName)
    }

    (conq: @unchecked) match {
      case s: Spine[T] =>
        rightmost(s.rwing.rightmost)
      case Tip(Zero) =>
        null
      case Tip(tip) =>
        rightmost(tip.rightmost)
      case Lazy(_, queue, _) =>
        last(queue)
    }
  }

  @tailrec def normalizeLeftWingsAndTip[T](
    conq: Conqueue[T], front: Conc[T]
  ): Conc[T] = {
    @tailrec def wrapUntil(
      s: Spine[T], wrapped: Conc[T], level: Int
    ): (Conc[T], Conqueue[T]) = {
      if (wrapped.level >= level) (wrapped, s)
      else {
        val nwrapped = wrapped <> s.lwing.normalized
        (s.rear: @unchecked) match {
          case st: Spine[T] => wrapUntil(st, nwrapped, level)
          case Tip(tip) => (nwrapped, s.rear)
        }
      }
    }

    (conq: @unchecked) match {
      case s: Spine[T] =>
        val (wrapped, remaining) = wrapUntil(s, Conc.Empty, math.max(1, front.level))
        normalizeLeftWingsAndTip(remaining, front <> wrapped)
      case Tip(tip) =>
        front <> tip.normalized
    }
  }

  @tailrec def normalizeRightWings[T](conq: Conqueue[T], back: Conc[T]): Conc[T] = {
    @tailrec def wrapUntil(
      s: Spine[T], wrapped: Conc[T], level: Int
    ): (Conc[T], Conqueue[T]) = {
      if (wrapped.level >= level) (wrapped, s)
      else {
        val nwrapped = s.rwing.normalized <> wrapped
        (s.rear: @unchecked) match {
          case st: Spine[T] => wrapUntil(st, nwrapped, level)
          case Tip(tip) => (nwrapped, Tip(Zero))
        }
      }
    }

    (conq: @unchecked) match {
      case s: Spine[T] =>
        val (wrapped, remaining) = wrapUntil(s, Conc.Empty, math.max(1, back.level))
        normalizeRightWings(remaining, wrapped <> back)
      case Tip(tip) =>
        back
    }
  }

  def toLazyConqueue[T](xs: Conc[T]): Conqueue.Lazy[T] = Lazy(Nil, toConqueue(xs), Nil)

  def toConqueue[T](xs: Conc[T], log: Log = noLog): Conqueue[T] = xs match {
    case conq: Conqueue[T] => conq
    case Append(_, _) => toConqueue(xs.normalized)
    case num: Num[T] => toConqueue(num.normalized)
    case Empty => Tip(Zero)
    case leaf: Leaf[T] => Tip(One(leaf))
    case xs @ _ <> _ => unwrap(xs, log)
    case _ => ???
  }

  case class Partial[T](rank: Int, bucket: List[Conc[T]], stack: List[Num[T]]) {
    def lborrow(): Partial[T] = {
      if (stack.head.digit == 1) copy(stack = stack.tail, rank = rank - 1)
      else copy(stack = noBorrowPopLast(stack.head) :: stack.tail)
    }
    def rborrow(): Partial[T] = {
      if (stack.head.digit == 1) copy(stack = stack.tail, rank = rank - 1)
      else copy(stack = noBorrowPopHead(stack.head) :: stack.tail)
    }
  }

  private def unwrap[T](xs: <>[T], log: Log = noLog): Conqueue[T] = {
    def zip(rank: Int, lstack: List[Num[T]], rstack: List[Num[T]]): Conqueue[T] =
      ((lstack, rstack): @unchecked) match {
        case (lwing :: Nil, Nil) =>
          assert(lwing.leftmost.level == rank)
          Tip(lwing)
        case (Nil, rwing :: Nil) =>
          assert(rwing.rightmost.level == rank)
          Tip(rwing)
        case (lwing :: Nil, rwing :: Nil) =>
          assert(lwing.leftmost.level == rank)
          assert(rwing.rightmost.level == rank)
          new Spine(lwing, rwing, Tip(Zero))
        case (lwing :: ltail, rwing :: rtail) =>
          new Spine(lwing, rwing, zip(rank + 1, ltail, rtail))
      }

    //def unwrap = unwrap1 _
    @tailrec
    def unwrap(
      lstack: List[Num[T]], rstack: List[Num[T]], rem: Conqueue[Conc[T]]
    ): (List[Num[T]], List[Num[T]]) = {
      if (rem.isEmpty) (lstack.reverse, rstack.reverse)
      else if (lstack.length < rstack.length) {
        val remhead = rem.head
        if (
          (lstack.nonEmpty && lstack.head.rightmost.level < remhead.level) ||
          (lstack.isEmpty && remhead.level > 0)
        ) {
          val nrem = remhead.left +: remhead.right +: rem.tail
          unwrap(lstack, rstack, nrem)
        } else (lstack: @unchecked) match {
          case Three(_1, _2, _3) :: ltail =>
            val added = _3 <> remhead
            if (added.level == _3.level)
              unwrap(Three(_1, _2, added) :: ltail, rstack, rem.tail)
            else unwrap(One(added) :: Two(_1, _2) :: ltail, rstack, rem.tail)
          case Two(_1, _2) :: ltail =>
            val added = _2 <> remhead
            if (added.level == _2.level)
              unwrap(Two(_1, added) :: ltail, rstack, rem.tail)
            else unwrap(One(added) :: One(_1) :: ltail, rstack, rem.tail)
          case One(_1) :: Nil =>
            val added = _1 <> remhead
            unwrap(Two(added.left, added.right) :: Nil, rstack, rem.tail)
          case One(_1) :: num :: ltail =>
            val added = _1 <> remhead
            val shaken = if (added.level == _1.level) added else shakeRight(added)
            if (shaken.level == _1.level)
              unwrap(One(shaken) :: num :: ltail, rstack, rem.tail)
            else if (shaken.left.level == shaken.right.level)
              unwrap(Two(shaken.left, shaken.right) :: num :: ltail, rstack, rem.tail)
            else num match {
              case Three(n1, n2, n3) =>
                unwrap(
                  Two(n3 <> shaken.left, shaken.right) :: Two(n1, n2) :: ltail,
                  rstack, rem.tail)
              case num =>
                unwrap(
                  One(shaken.right) :: noCarryPushLast(num, shaken.left) :: ltail,
                  rstack, rem.tail)
            }
          case Nil =>
            unwrap(One(remhead) :: Nil, rstack, rem.tail)
        }
      } else {
        val remlast = rem.last
        if (
          (rstack.nonEmpty && rstack.head.leftmost.level < remlast.level) ||
          (rstack.isEmpty && remlast.level > 0)
        ) {
          val nrem = rem.init :+ remlast.left :+ remlast.right
          unwrap(lstack, rstack, nrem)
        } else (rstack: @unchecked) match {
          case Three(_1, _2, _3) :: rtail =>
            val added = remlast <> _1
            if (added.level == _1.level)
              unwrap(lstack, Three(added, _2, _3) :: rtail, rem.init)
            else unwrap(lstack, One(added) :: Two(_2, _3) :: rtail, rem.init)
          case Two(_1, _2) :: rtail =>
            val added = remlast <> _1
            if (added.level == _1.level)
              unwrap(lstack, Two(added, _2) :: rtail, rem.init)
            else unwrap(lstack, One(added) :: One(_2) :: rtail, rem.init)
          case One(_1) :: Nil =>
            val added = remlast <> _1
            unwrap(lstack, Two(added.left, added.right) :: Nil, rem.init)
          case One(_1) :: num :: ltail =>
            val added = remlast <> _1
            val shaken = if (added.level == _1.level) added else shakeLeft(added)
            if (shaken.level == _1.level)
              unwrap(lstack, One(shaken) :: num :: ltail, rem.init)
            else if (shaken.left.level == shaken.right.level)
              unwrap(lstack, Two(shaken.left, shaken.right) :: num :: ltail, rem.init)
            else num match {
              case Three(n1, n2, n3) =>
                unwrap(lstack,
                  Two(shaken.left, shaken.right <> n1) :: Two(n2, n3) :: ltail,
                  rem.init)
              case num =>
                unwrap(lstack,
                  One(shaken.left) :: noCarryPushHead(num, shaken.right) :: ltail,
                  rem.init)
            }
          case Nil =>
            unwrap(lstack, One(remlast) :: Nil, rem.init)
        }
      }
    }

    val (lwings, rwings) = unwrap(Nil, Nil, Tip(One(new Single(xs))))
    zip(0, lwings, rwings)
  }

  def split[@specialized(Int, Long, Float, Double) T: ClassTag](
    xs: Conc[T], n: Int, rref: ObjectRef[Conc[T]]
  ): Conc[T] = (xs.normalized: @unchecked) match {
    case left <> right =>
      if (n < left.size) {
        val ll = split(left, n, rref)
        val lr = rref.elem
        rref.elem = lr <> right
        ll
      } else if (n > left.size) {
        val rl = split(right, n - left.size, rref)
        val rr = rref.elem
        rref.elem = rr
        left <> rl
      } else {
        rref.elem = right
        left
      }
    case s: Single[T] =>
      if (n == 0) {
        rref.elem = s
        Empty
      } else {
        rref.elem = Empty
        s
      }
    case c: Chunk[T] =>
      def subchunk(from: Int, sz: Int) = {
        if (sz == 0) Empty
        else new Chunk(copiedArray(c.array, from, sz), sz, c.k)
      }
      val lelems = n
      val relems = c.size - n
      val ltree = subchunk(0, n)
      val rtree = subchunk(n, c.size - n)
      rref.elem = rtree
      ltree
    case Empty =>
      rref.elem = Empty
      Empty
    case _ =>
      invalid("All cases should have been covered: " + xs + ", " + xs.getClass)
  }

  def isEmptyConqueue[T](conqueue: Conqueue[T]): Boolean = conqueue match {
    case Lazy(_, Tip(Zero), _) => true
    case Tip(Zero) => true
    case _ => false
  }

  trait Log {
    def apply(x: AnyRef): Unit
    def on: Boolean
    def clear() {}
    def flush() {}
  }

  object noLog extends Log {
    def apply(x: AnyRef) {}
    def on = false
  }

  object printLog extends Log {
    def apply(x: AnyRef) = println(x.toString)
    def on = true
  }

  def bufferedLog(proxy: Log) = new Log {
    val buffer = collection.mutable.Buffer[String]()
    def apply(x: AnyRef) = buffer += x.toString
    def on = true
    override def clear() = buffer.clear()
    override def flush() {
      proxy(buffer.mkString("\n"))
      clear()
    }
  }

}
