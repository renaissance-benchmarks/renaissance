package io.reactors
package debugger



import io.reactors.concurrent.Frame



/** A debugger API implementation that ignores all debugger actions.
 */
class ZeroDebugApi(val system: ReactorSystem) extends DebugApi {
  def isEnabled = false

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

  def log(x: Any){
  }

  def shutdown() {
  }
}
