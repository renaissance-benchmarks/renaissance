package io.reactors



import io.reactors.concurrent.Frame



/** Debugger interface for the reactor system.
 */
abstract class DebugApi extends Platform.Reflectable {
  /** Returns `true` iff debugging is currently enabled.
   */
  def isEnabled: Boolean

  /** Called when an event is sent on a channel.
   */
  def eventSent[@spec(Int, Long, Double) T](c: Channel[T], x: T): Unit

  /** Called by a reactor when an event is delivered.
   */
  def eventDelivered[@spec(Int, Long, Double) T](c: Channel[T], x: T): Unit

  /** Called when a reactor starts.
   */
  def reactorStarted(f: Frame): Unit

  /** Called when a reactor is scheduled, i.e. gets execution time on some CPU.
   */
  def reactorScheduled(r: Reactor[_]): Unit

  /** Called when a reactor is preempted by the scheduler.
   */
  def reactorPreempted(r: Reactor[_]): Unit

  /** Called when a reactor dies due to an error.
   */
  def reactorDied(r: Reactor[_]): Unit

  /** Called when a reactor terminates.
   */
  def reactorTerminated(r: Reactor[_]): Unit

  /** Called when a connector is created.
   */
  def connectorOpened[T](c: Connector[T]): Unit

  /** Called when a connector is sealed.
   */
  def connectorSealed[T](c: Connector[T]): Unit

  /** Print the specified message to the debugger.
   */
  def log(x: Any): Unit

  /** Shuts down the debugger.
   */
  def shutdown(): Unit
}


object DebugApi {
}
