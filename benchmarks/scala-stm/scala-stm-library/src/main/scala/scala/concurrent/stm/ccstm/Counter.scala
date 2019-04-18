/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm.ccstm

import java.util.concurrent.atomic.AtomicLong
import scala.annotation.tailrec

/** A counter with a linearizable increment operator and adaptive contention
 *  avoidance.  Reading the counter with `apply()` is not linearizable (unless
 *  the only delta passed to += is 1) and is not optimized.
 */
private[ccstm] class Counter extends {
  private final val MaxStripes = 64

  // this doesn't need to be volatile because when we grow it we retain all of
  // the old AtomicLong-s
  private var _stripes = Array(new AtomicLong)

  private def grow() {
    synchronized {
      if (_stripes.length < MaxStripes) {
        val repl = new Array[AtomicLong](_stripes.length * 2)
        System.arraycopy(_stripes, 0, repl, 0, _stripes.length)
        var i = _stripes.length
        while (i < repl.length) {
          repl(i) = new AtomicLong
          i += 1
        }
        _stripes = repl
      }
    }
  }

  def += (delta: Int) {
    if (delta != 0)
      incr(delta)
  }

  @tailrec private def incr(delta: Int) {
    val s = _stripes
    val i = CCSTM.hash(Thread.currentThread) & (s.length - 1)
    val prev = s(i).get
    if (!s(i).compareAndSet(prev, prev + delta)) {
      grow()
      incr(delta)
    }
  }

  def apply(): Long = _stripes.foldLeft(0L)( _ + _.get )

  override def toString = apply().toString
}
