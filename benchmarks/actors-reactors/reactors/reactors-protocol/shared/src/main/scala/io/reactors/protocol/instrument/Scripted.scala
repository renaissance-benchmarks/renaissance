package io.reactors.protocol.instrument



import io.reactors._



/** Service used to record custom channel and reactor behavior.
 *
 *  Together with the `ScriptedTransport`, this service is used to simulate
 *  faulty behavior and unreliable network, or otherwise any kind of special behavior.
 */
class Scripted(val system: ReactorSystem) extends Protocol.Service {
  /** Modifies the behavior of a specific channel.
   *
   *  Takes a behavior function that maps an event stream of emitted events on this
   *  channel to an event stream of delivered events.
   *  Calling this operation overwrites any behaviors installed with previous calls
   *  with the specific channel.
   *
   *  @tparam T          the type of events on the channel
   *  @param ch          the channel whose delivery semantics must be changed
   *  @param behavior    a function that specifies how the stream of events that were
   *                     emitted on this channel must be altered into another event
   *                     stream to simulate some sort of special behavior
   */
  def instrument[T](ch: Channel[T])(behavior: Events[T] => Events[T]): Unit = {
    val transport = system.remote.transport("scripted").asInstanceOf[ScriptedTransport]
    transport.withChannel(ch, behavior)
  }

  override def shutdown(): Unit = {
  }
}


object Scripted {
  val defaultBundle: ReactorSystem.Bundle = ReactorSystem.Bundle.default("""
    remote = {
      default-schema = "scripted"
      transports = [
        {
          schema = "scripted"
          transport = "io.reactors.protocol.instrument.ScriptedTransport"
          host = ""
          port = 0
        }
      ]
    }
    system = {
      channels = {
        create-as-local = "false"
      }
    }
  """.stripMargin)
}
