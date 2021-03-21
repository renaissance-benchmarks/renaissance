package io.reactors
package protocol






/** Utilities that manipulate and transform channels.
 */
trait ChannelProtocols {
  import scala.language.implicitConversions

  implicit def channelOps[@spec(Int, Long, Double) T: Arrayable](ch: Channel[T]): ChannelProtocols.ChannelOps[T] =
    new ChannelProtocols.ChannelOps(ch)
}


object ChannelProtocols {
  class ChannelOps[@spec(Int, Long, Double) T: Arrayable](val ch: Channel[T]) {
    /** Returns a channel that executes a side-effect and forwards to the original.
     *
     *  @param f       side-effect to execute before forwarding an event
     *  @return        the new channel
     */
    def inject(f: T => Unit): Channel[T] = {
      val system = Reactor.self.system
      val c = system.channels.daemon.shortcut.open[T]
      c.events onEvent { x =>
        f(x)
        ch ! x
      }
      c.channel
    }
  }
}
