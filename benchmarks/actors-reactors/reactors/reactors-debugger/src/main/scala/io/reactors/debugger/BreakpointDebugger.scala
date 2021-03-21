package io.reactors
package debugger



import io.reactors.common.UnrolledRing
import io.reactors.concurrent.Frame
import java.util.concurrent.atomic.AtomicLong
import scala.collection._



class BreakpointDebugger(val system: ReactorSystem, val deltaDebugger: DeltaDebugger) {
  import BreakpointDebugger.Breakpoint

  private val monitor = system.monitor
  private val bidCounter = new AtomicLong
  private val breakpoints = mutable.Map[Long, Breakpoint]()

  def isEnabled = true

  def eventSent[@spec(Int, Long, Double) T](c: Channel[T], x: T) {
  }

  def eventDelivered[@spec(Int, Long, Double) T](c: Channel[T], x: T) {
  }

  def reactorStarted(f: Frame) {
  }

  def reactorScheduled(r: Reactor[_]) {
  }

  def reactorPreempted(r: Reactor[_]) {
  }

  def reactorDied(r: Reactor[_]) {
  }

  def reactorTerminated(r: Reactor[_]) {
  }

  def connectorOpened[T](c: Connector[T]) {
  }

  def connectorSealed[T](c: Connector[T]) {
  }

  def log(x: Any) {
  }

  def breakpointAdd(pattern: String, tpe: String): Long =
    monitor.synchronized {
      val bid = bidCounter.getAndIncrement()
      val b = new Breakpoint(bid, pattern, tpe)
      breakpoints(bid) = b
      bid
    }

  def breakpointList(): List[Breakpoint] = monitor.synchronized {
    breakpoints.values.toList
  }

  def breakpointRemove(bid: Long): Option[Breakpoint] = monitor.synchronized {
    breakpoints.remove(bid)
  }
}


object BreakpointDebugger {
  class Breakpoint(val bid: Long, val pattern: String, val tpe: String)
}
