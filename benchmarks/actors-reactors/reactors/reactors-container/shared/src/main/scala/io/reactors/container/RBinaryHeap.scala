package io.reactors
package container



import scala.collection._
import scala.annotation.implicitNotFound
import io.reactors.common.BinaryHeap



/** Reactive binary heap.
 *
 *  Exposes a signal `head`, used to probe or subscribe to changes to
 *  the first element in the heap.
 *
 *  @tparam T            type of the elements in the heap
 *  @param initialSize   initial size of the internal array
 */
class RBinaryHeap[@spec(Int, Long, Double) T](val initialSize: Int = 16)(
  implicit val arrayable: Arrayable[T],
  val order: Order[T]
) extends RContainer.Modifiable {
  private[reactors] var heap: BinaryHeap[T] = _
  private[reactors] var insertsEmitter: Events.Emitter[T] = _
  private[reactors] var removesEmitter: Events.Emitter[T] = _
  private[reactors] var headCell: RCell[T] = _

  def init(dummy: RBinaryHeap[T]) {
    heap = new BinaryHeap(initialSize)
    insertsEmitter = new Events.Emitter[T]
    removesEmitter = new Events.Emitter[T]
    headCell = new RCell[T](nil)
  }

  init(this)

  def nil = arrayable.nil

  def foreach(f: T => Unit): Unit = heap.foreach(f)

  def size = heap.size

  def inserts = insertsEmitter

  def removes = removesEmitter

  def enqueue(elem: T): Unit = try {
    acquireModify()
    assert(elem != nil)
    val oldHead = if (heap.nonEmpty) heap.head else arrayable.nil
    heap.enqueue(elem)
    val newHead = heap.head
    insertsEmitter.react(elem)
    if (newHead != oldHead) headCell := newHead
  } finally releaseModify()

  def dequeue(): T = try {
    acquireModify()
    val elem = heap.dequeue()
    removesEmitter.react(elem)
    if (size > 0) headCell := heap.head
    else headCell := nil
    elem
  } finally releaseModify()

  def head: Signal[T] = headCell

}
