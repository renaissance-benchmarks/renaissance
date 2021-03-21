package io.reactors



import io.reactors.concurrent.Frame
import scala.concurrent.ExecutionContext



object JsScheduler {
  /** Scheduler that uses the global JS execution context.
   *
   *  This executes the submitted tasks one-by-one, in a serial manner.
   */
  class GlobalQueue extends Scheduler {
    def schedule(frame: Frame): Unit = {
      val r = frame.schedulerState.asInstanceOf[Runnable]
      ExecutionContext.Implicits.global.execute(r)
    }

    override def newState(frame: Frame): Scheduler.State = {
      new Scheduler.State.Default with Runnable {
        def run() = {
          try frame.executeBatch()
          catch {
            case t: Throwable =>
              frame.reactorSystem.errorHandler(t)
          }
        }
      }
    }
  }

  /** Default scheduler for the JS platform.
   *
   *  Uses a global queue of pending tasks, and executes them one-by-one.
   */
  lazy val default: Scheduler = new GlobalQueue

  object Key {
    /** Key of the default scheduler for the JS platform.
     */
    val default = "org.reactors.JsScheduler::default"
    def defaultScheduler = default
  }
}
