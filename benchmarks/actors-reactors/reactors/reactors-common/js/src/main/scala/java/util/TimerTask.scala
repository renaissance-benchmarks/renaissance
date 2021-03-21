package java.util

import scala.concurrent.duration.FiniteDuration
import scala.scalajs.js.timers._
import scala.scalajs.js.timers.SetTimeoutHandle

abstract class TimerTask {
  private[util] var owner: Timer = null
  private[util] var canceled: Boolean = false
  private[util] var completed: Boolean = false
  private[util] var lastScheduled: Long = 0L
  private[util] var handle: SetTimeoutHandle = null

  def run(): Unit

  def cancel(): Boolean = {
    if (handle != null) {
      clearTimeout(handle)
      handle = null
    }
    if (canceled || owner == null || completed) {
      canceled = true
      false
    } else {
      canceled = true
      true
    }
  }

  def scheduledExecutionTime(): Long = lastScheduled

  private[util] def timeout(delay: FiniteDuration)(body: => Unit) = {
    if (!canceled) {
      handle = setTimeout(delay)(body)
    }
  }

  private[util] def doRun() {
    if (!canceled && !owner.canceled) {
      lastScheduled = System.currentTimeMillis()
      try {
        run()
      } catch {
        case t: Throwable =>
          canceled = true
          completed = true
          throw t
      }
    }
  }

}
