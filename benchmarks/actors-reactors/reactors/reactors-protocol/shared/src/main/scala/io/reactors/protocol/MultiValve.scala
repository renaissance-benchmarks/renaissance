package io.reactors
package protocol



import io.reactors.container.RHashSet
import io.reactors.container.RRing
import scala.annotation.unchecked



/** Collection that stores `Valve` objects, and acts as a `Valve` itself.
 */
class MultiValve[@specialized(Int, Long, Double) T: Arrayable](val window: Int) {
  private[reactors] var ring: RRing[T] = _
  private[reactors] var valves: RHashSet[(Valve[T], RCell[Long])] = _
  private[reactors] var slowest: Signal[Long] = _
  private[reactors] var oldest: Long = _
  private[reactors] var next: RCell[Long] = _
  private[reactors] var flush: Connector[Unit] = _
  private[reactors] var rawOut: Valve[T] = _

  def init(self: MultiValve[T]) {
    ring = new RRing[T](window)
    valves = new RHashSet[(Valve[T], RCell[Long])]
    slowest = valves.map(_._2).toSignalAggregate(Long.MaxValue)(math.min)
    oldest = 0L
    next = RCell(0L)
    flush = Reactor.self.system.channels.daemon.open[Unit]
    flush.events on {
      val total = slowest() - oldest
      oldest += total
      ring.dequeueMany(total.toInt)
    }
    rawOut = {
      val c = Reactor.self.system.channels.daemon.shortcut.open[T]
      val forwarding = c.events onEvent { x =>
        if (ring.available()) {
          ring.enqueue(x)
          next := next() + 1
          if (slowest() > next()) ring.dequeue()
        } else throw new IllegalStateException("Valve is not available.")
      }
      Valve(
        c.channel,
        ring.available,
        forwarding.andThen(c.seal()).andThen(valves.clear()).andThen(flush.seal())
      )
    }
  }

  init(this)

  def size: Int = valves.size

  def bufferSize: Int = ring.size

  def out: Valve[T] = rawOut

  def +=(v: Valve[T]): Subscription = {
    val pos = RCell(math.min(slowest(), next()))
    valves += (v, pos)

    val morePending = (pos zip next)(_ < _).changes.toSignal(pos() < next())
    val available = (v.available zip morePending)(_ && _)
    val moving = available.is(true) on {
      while (available()) {
        val idx = (pos() - oldest).toInt
        val x = ring(idx)
        v.channel ! x
        pos := pos() + 1
      }
      val total = slowest() - oldest
      if (total > 0) flush.channel ! (())
    }

    moving.chain(available).chain(morePending).andThen(valves -= (v, pos))
  }
}


object MultiValve {
  /** Variant of multi-valve optimized for the case when it contains a single valve.
   */
  class Biased[@spec(Int, Long, Double) T: Arrayable](val window: Int) {
    private[reactors] var implementation: RCell[AnyRef] = _
    private[reactors] var rawOut: Valve[T] = _

    def init(self: Biased[T]) {
      implementation = RCell(null)
      rawOut = {
        val c = Reactor.self.system.channels.daemon.shortcut.open[T]
        c.events onEvent { x =>
          implementation() match {
            case null =>
            case v if v.isInstanceOf[Valve[_]] => v.asInstanceOf[Valve[T]].channel ! x
            case m: MultiValve[T] @unchecked => m.out.channel ! x
          }
        }
        val available = implementation.toEager.map({
          case null => RCell(true)
          case v if v.isInstanceOf[Valve[_]] => v.asInstanceOf[Valve[T]].available
          case m: MultiValve[_] => m.out.available
        }).mux.changed(false).toEmpty
        val sub = Subscription(c.seal()).andThen {
          implementation() match {
            case null =>
            case v if v.isInstanceOf[Valve[_]] =>
            case m: MultiValve[_] => m.out.subscription.unsubscribe()
          }
        }
        Valve(c.channel, available, sub)
      }
    }

    init(this)

    def out = rawOut

    def +=(v: Valve[T]): Subscription = {
      implementation() match {
        case null =>
          implementation := v
          Subscription(implementation := null)
        case w: Valve[T] @unchecked =>
          val multi = new MultiValve[T](window)
          multi += v
          val sub = multi += w
          implementation := multi
          sub
        case m: MultiValve[T] @unchecked =>
          m += v
      }
    }
  }
}
