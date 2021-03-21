package io.reactors.common



import scala.reflect.ClassTag



class ConqueueBuffer[@specialized(Byte, Char, Int, Long, Float, Double) T: ClassTag](
  val k: Int, val isLazy: Boolean, private var conqueue: Conqueue[T]
) {
  import Conc._
  import Conqueue._

  require(k > 0)

  private var leftChunk: Array[T] = _
  private var leftIndex: Int = k - 1
  private var leftStart: Int = k - 1
  private var rightChunk: Array[T] = _
  private var rightIndex: Int = 0
  private var rightStart: Int = 0

  private def init(dummy: ConqueueBuffer[T]) {
    leftChunk = new Array[T](k)
    leftIndex = k - 1
    leftStart = k - 1
    rightChunk = new Array[T](k)
    rightIndex = 0
    rightStart = 0
  }

  init(this)

  def this(k: Int) = this(k, true, Conqueue.Lazy(Nil, Conqueue.empty, Nil))

  def this(k: Int, lazyConqueue: Boolean) =
    this(k, lazyConqueue,
      if (lazyConqueue) Conqueue.Lazy(Nil, Conqueue.empty, Nil) else Conqueue.empty)

  def size = conqueue.size

  def isEmpty = {
    leftIndex == leftStart && ConcUtils.isEmptyConqueue(conqueue) &&
    rightIndex == rightStart
  }

  def nonEmpty = !isEmpty

  private def leftEnsureSize(n: Int) {
    if (leftChunk.length < n) leftChunk = new Array[T](n)
  }

  private def rightEnsureSize(n: Int) {
    if (rightChunk.length < n) rightChunk = new Array[T](n)
  }

  private def pullLeft() {
    if (conqueue.nonEmpty) {
      val head = ConcUtils.head(conqueue)
      conqueue = ConcUtils.popHeadTop(conqueue)
      (head: @unchecked) match {
        case head: Chunk[T] =>
          leftChunk = head.array
          leftStart = head.size - 1
          leftIndex = -1
        case head: Single[T] =>
          leftChunk = new Array[T](k)
          leftChunk(k - 1) = head.x
          leftStart = k - 1
          leftIndex = k - 2
      }
    } else if (rightIndex > rightStart) {
      val rightMid = (rightStart + rightIndex + 1) / 2
      val n = rightMid - rightStart
      leftEnsureSize(n)
      System.arraycopy(rightChunk, rightStart, leftChunk, leftChunk.length - n, n)
      rightStart = rightMid
      leftStart = leftChunk.length - 1
      leftIndex = leftChunk.length - n - 1
    } else unsupported("empty")
  }

  def head: T = {
    if (leftIndex < leftStart) leftChunk(leftIndex + 1)
    else {
      pullLeft()
      head
    }
  }

  private def pullRight() = {
    if (conqueue.nonEmpty) {
      val last = ConcUtils.last(conqueue)
      conqueue = ConcUtils.popLastTop(conqueue)
      (last: @unchecked) match {
        case last: Chunk[T] =>
          rightChunk = last.array
          rightStart = 0
          rightIndex = last.size
        case last: Single[T] =>
          rightChunk = new Array[T](k)
          rightChunk(0) = last.x
          rightStart = 0
          rightIndex = 1
      }
    } else if (leftIndex < leftStart) {
      val leftMid = (leftIndex + 1 + leftStart) / 2
      val n = leftStart - leftMid + 1
      rightEnsureSize(n)
      System.arraycopy(leftChunk, leftMid, rightChunk, 0, n)
      leftStart = leftMid - 1
      rightStart = 0
      rightIndex = n
    } else unsupported("empty")
  }

  def last: T = {
    if (rightIndex > rightStart) rightChunk(rightIndex - 1)
    else {
      pullRight()
      last
    }
  }

  private def packLeft(): Unit = if (leftIndex < leftStart) {
    val sz = leftStart - leftIndex
    val chunk = {
      if (leftIndex == -1) leftChunk
      else ConcUtils.copiedArray(leftChunk, leftIndex + 1, sz)
    }
    conqueue = ConcUtils.pushHeadTop(conqueue, new Chunk(chunk, sz, k))
  }

  private def expandLeft() {
    packLeft()
    leftChunk = new Array[T](k)
    leftIndex = k - 1
    leftStart = k - 1
  }

  private def packRight(): Unit = if (rightIndex > rightStart) {
    val sz = rightIndex - rightStart
    val chunk = {
      if (rightStart == 0) rightChunk
      else ConcUtils.copiedArray(rightChunk, rightStart, sz)
    }
    conqueue = ConcUtils.pushLastTop(conqueue, new Chunk(chunk, sz, k))
  }

  private def expandRight() {
    packRight()
    rightChunk = new Array[T](k)
    rightIndex = 0
    rightStart = 0
  }

  def pushHead(elem: T): this.type = {
    if (leftIndex < 0) expandLeft()
    leftChunk(leftIndex) = elem
    leftIndex -= 1
    this
  }

  def +=:(elem: T): this.type = pushHead(elem)

  def popHead(): T = {
    if (leftIndex < leftStart) {
      leftIndex += 1
      val result = leftChunk(leftIndex)
      leftChunk(leftIndex) = null.asInstanceOf[T]
      result
    } else {
      pullLeft()
      popHead()
    }
  }

  def pushLast(elem: T): this.type = {
    if (rightIndex > rightChunk.size - 1) expandRight()
    rightChunk(rightIndex) = elem
    rightIndex += 1
    this
  }

  def +=(elem: T): this.type = pushLast(elem)

  def popLast(): T = {
    if (rightIndex > rightStart) {
      rightIndex -= 1
      val result = rightChunk(rightIndex)
      rightChunk(rightIndex) = null.asInstanceOf[T]
      result
    } else {
      pullRight()
      popLast()
    }
  }

  def extractConqueue() = {
    packLeft()
    packRight()
    var result = conqueue
    conqueue = if (isLazy) Lazy(Nil, Conqueue.empty, Nil) else Conqueue.empty
    result
  }

  def clear() {
    init(this)
  }

  override def toString = {
    val buffer = collection.mutable.Buffer[T]()
    for (i <- (leftIndex + 1) to leftStart) buffer += leftChunk(i)
    for (x <- conqueue) buffer += x
    for (i <- rightStart until rightIndex) buffer += rightChunk(i)
    buffer.mkString("ConqueueBuffer(", ", ", ")")
  }

  private[common] def diagnosticString = {
    println(s"-----------")
    println(s"leftIndex/leftStart: $leftIndex/$leftStart")
    println(s"leftChunk:  ${leftChunk.mkString(", ")}")
    println(s"rightStart/rightIndex: $rightStart/$rightIndex")
    println(s"rightChunk: ${rightChunk.mkString(", ")}")
    println(s"mid: ${ConcUtils.toSeq(conqueue).mkString(", ")}")
  }

}









