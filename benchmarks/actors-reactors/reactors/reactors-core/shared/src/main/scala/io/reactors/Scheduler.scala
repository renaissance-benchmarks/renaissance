package io.reactors



import io.reactors.concurrent._



/** An object that schedules reactors for execution.
 *
 *  After a reactor is instantiated, its reactor frame is assigned a scheduler by the
 *  reactor system.
 *  A reactor that is assigned a specific scheduler will always be executed on that
 *  same scheduler.
 *
 *  After creating a reactor, every reactor system will first call the `initSchedule`
 *  method on the reactor frame.
 *  Then, the reactor system will call the `schedule` method every time there are events
 *  ready for the reactor.
 *
 *  '''Note:'''
 *  Clients never invoke `Scheduler` operations directly,
 *  but can implement their own scheduler if necessary.
 *
 *  @see [[org.reactors.ReactorSystem]]
 */
trait Scheduler {
  /** Notifies a reactor frame that it should be executed.
   *  Clients never call this method directly.
   *
   *  This method uses the reactor frame to flush messages from its event queue
   *  and propagate events through the reactor.
   *
   *  @param frame      the reactor frame to schedule
   */
  def schedule(frame: Frame): Unit

  /** Tells the scheduler to start listening to schedule requests for the reactor frame.
   *  Clients never call this method directly.
   *
   *  By default, assigns the default scheduler state to the `schedulerState` field in
   *  the reactor frame.
   *
   *  @param frame      the reactor frame to start scheduling
   */
  def initSchedule(frame: Frame): Unit = {
    frame.schedulerState = newState(frame)
  }

  /** Called immediately before a reactor frame begins an execution batch.
   */
  def preschedule(system: ReactorSystem): Unit = {}

  /** Called immediately after a reactor frame completes an execution batch.
   *
   *  Optionally unschedules and runs some number of frames previously scheduled.
   *
   *  This method by default does nothing, but may be overridden for performance
   *  purposes.
   */
  def postschedule(system: ReactorSystem, t: Throwable): Unit = {}

  /** Creates an `State` object for the reactor frame.
   *
   *  @param frame       the reactor frame
   *  @return            creates a fresh scheduler info object
   */
  protected def newState(frame: Frame): Scheduler.State = new Scheduler.State.Default {}
}


/** Companion object for creating standard reactor schedulers.
 */
object Scheduler {

  /** Superclass for the information objects that a scheduler attaches to a reactor
   *  frame.
   */
  trait State {
    /** Called when a batch of events are about to be handled.
     *  
     *  @param frame    the reactor frame
     */
    def onBatchStart(frame: Frame): Unit = {
    }

    /** Called just before an event gets scheduled.
     *  
     *  @param frame    the reactor frame
     *  @return         `true` if scheduler can consume more events, `false` otherwise
     */
    def onBatchEvent(frame: Frame): Boolean
  }

  object State {
    /** The default info object implementation.
     */
    trait Default extends State {
      @volatile var allowedBudget: Long = _

      override def onBatchStart(frame: Frame): Unit = {
        allowedBudget = frame.reactorSystem.bundle.schedulerConfig.defaultBudget
      }

      def onBatchEvent(frame: Frame): Boolean = {
        allowedBudget -= 1
        allowedBudget > 0
      }
    }
  }

  /** Forwards all scheduling calls to a different scheduler.
   */
  class Proxy(val target: Scheduler) extends Scheduler {
    def schedule(f: Frame) = target.schedule(f)

    override def initSchedule(f: Frame) = target.initSchedule(f)

    override def preschedule(system: ReactorSystem) = target.preschedule(system)

    override def postschedule(system: ReactorSystem, t: Throwable): Unit =
      target.postschedule(system, t)

    protected override def newState(frame: Frame): Scheduler.State =
      target.newState(frame)
  }
}
