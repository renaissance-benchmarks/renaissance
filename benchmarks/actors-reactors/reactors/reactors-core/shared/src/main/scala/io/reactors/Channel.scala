package io.reactors



import io.reactors.concurrent.Frame
import scala.collection._



/** `Channel` is a shareable reference to a writing endpoint of a reactor.
 *
 *  By calling the channel's `!` method, an event is sent to the channel. The event is
 *  eventually emitted on the channel's corresponding event stream, which is readable
 *  only by the reactor that owns that channel.
 *
 *  @tparam T       type of the events propagated by this channel
 */
trait Channel[@spec(Int, Long, Double) T] extends Channel.LowPriority[T] {
  /** Sends a single event on this channel.
   *
   *  @param x      event sent to the channel
   */
  def send(x: T): Unit
}


/** Default channel implementations.
 */
object Channel {
  /** Low priority supertype, used to hook the default implicit conversion for `!`.
   */
  trait LowPriority[@spec(Int, Long, Double) T] {
    def send(x: T): Unit
  }

  class Shared[@spec(Int, Long, Double) T: Arrayable](
    val url: ChannelUrl,
    @transient var underlying: Channel[T]
  ) extends Channel[T] with Serializable {
    private[reactors] def resolve(system: ReactorSystem): Unit = {
      underlying = system.remote.resolve[T](url)
    }

    def send(x: T): Unit = {
      // TODO: Make initialization thread-safe.
      if (underlying == null) {
        resolve(Reactor.self.system)
      }
      underlying ! x
    }
  }

  class Zero[@spec(Int, Long, Double) T] extends Channel[T] {
    def send(x: T) = {}
  }

  class Failed[@spec(Int, Long, Double) T] extends Channel[T] {
    def send(x: T) = sys.error("Failed channel cannot deliver messages.")
  }

  class Local[@spec(Int, Long, Double) T](
    val system: ReactorSystem,
    val uid: Long,
    val frame: Frame,
    val shortcut: Boolean
  ) extends Channel[T] with Identifiable {
    private[reactors] var connector: Connector[T] = _
    private[reactors] var isOpen = true

    def send(x: T): Unit = {
      system.debugApi.eventSent(this, x)
      if (isOpen) {
        if (shortcut && (Reactor.currentFrame eq frame)) {
          connector.queue.bypass(x)
        } else frame.enqueueEvent(connector, x)
      }
    }

    def isSealed: Boolean = !isOpen
  }
}
