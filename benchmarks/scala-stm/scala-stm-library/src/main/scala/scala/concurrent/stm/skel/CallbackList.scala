/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package skel

import annotation.tailrec


private[stm] class CallbackList[A] {

  private final val InitialCapacity = 128
  private final val MaxEmptyCapacity = 8192

  private var _size = 0
  private var _data = new Array[A => Unit](InitialCapacity)

  def isEmpty: Boolean = _size == 0

  def size: Int = _size

  def size_= (newSize: Int) {
    if (newSize != _size)
      changeSize(newSize)
  }

  private def changeSize(newSize: Int) {
    if (newSize < 0 || newSize > _size)
      throw new IllegalArgumentException

    if (newSize == 0 && _data.length > MaxEmptyCapacity) {
      // reallocate if the array is too big, so that a single large txn doesn't
      // permanently increase the memory footprint of this thread
      reset()
    } else {
      java.util.Arrays.fill(_data.asInstanceOf[Array[AnyRef]], newSize, _size, null)
      _size = newSize
    }
  }

  private def reset() {
    _data = new Array[A => Unit](InitialCapacity)
    _size = 0
  }

  def += (handler: A => Unit) {
    if (_size == _data.length)
      grow
    _data(_size) = handler
    _size += 1
  }

  private def grow() {
    val a = new Array[A => Unit](_data.length * 2)
    System.arraycopy(_data, 0, a, 0, _data.length)
    _data = a
  }

  def apply(i: Int): (A => Unit) = _data(i)

  def fire(level: NestingLevel, arg: A) {
    if (_size > 0)
      fire(level, arg, 0)
  }

  @tailrec private def fire(level: NestingLevel, arg: A, i: Int) {
    if (i < _size && shouldFire(level)) {
      try {
        _data(i)(arg)
      } catch {
        case x: Throwable => {
          val s = level.requestRollback(Txn.UncaughtExceptionCause(x))
          assert(s.isInstanceOf[Txn.RolledBack])
        }
      }
      fire(level, arg, i + 1)
    }
  }

  private def shouldFire(level: NestingLevel): Boolean = !level.status.isInstanceOf[Txn.RolledBack]

  /** Sets the size of this callback list to `newSize`, and returns a the
   *  discarded handlers.
   */
  def truncate(newSize: Int): Array[A => Unit] = {
    if (_size == newSize) {
      // nothing to do
      null
    } else {
      // copy
      val z = new Array[A => Unit](_size - newSize)
      System.arraycopy(_data, newSize, z, 0, z.length)
      size = newSize
      z
    }
  }
}
