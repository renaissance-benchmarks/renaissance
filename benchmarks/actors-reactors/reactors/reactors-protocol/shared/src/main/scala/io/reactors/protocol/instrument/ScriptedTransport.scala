package io.reactors.protocol.instrument



import io.reactors._
import scala.collection._



/** Transport whose reliability can be scripted.
 *
 *  When used, the corresponding reactor system must have its configuration property
 *  `system.channels.create-as-local` set to `"false"`. In addition, this transport
 *  must be present in the `remote` section of configuration.
 *
 *  The main use of this class is for testing - it allows simulating unreliability on
 *  the network level, as well as specific failure scenarios. This transport class
 *  itself is not meant to be used directly, but is used by the `Scripted` service.
 */
class ScriptedTransport(val system: ReactorSystem) extends Remote.Transport {
  lazy val multiplexer = system.spawn(Proto[ScriptedMultiplexer])

  private[instrument] def withChannel[T](
    ch: Channel[T], transform: Events[T] => Events[T]
  ): Unit = {
    val sharedChannel = ch.asInstanceOf[Channel.Shared[T]]
    val scriptedChannel =
      sharedChannel.underlying.asInstanceOf[ScriptedTransport.ScriptedChannel[Any]]

    val behave = ScriptedTransport.Behave(scriptedChannel, behaviors => {
      val emits = new Events.Emitter[T]
      val deliveries = transform(emits)
      val localChannel = system.channels.getLocal[T](sharedChannel.url).get
      val subscription = deliveries.onEventOrDone {
        x => localChannel ! x
      } {
        behaviors.remove(scriptedChannel)
      }
      (emits.asInstanceOf[Events.Emitter[Any]], subscription)
    })

    multiplexer ! behave
  }

  def schema = "scripted"

  def port = -1

  def newChannel[@spec(Int, Long, Double) T: Arrayable](url: ChannelUrl): Channel[T] = {
    new ScriptedTransport.ScriptedChannel(this, url)
  }

  override def shutdown(): Unit = {
    multiplexer ! ScriptedTransport.Clear()
  }
}


object ScriptedTransport {
  private[instrument] type Behavior = (Events.Emitter[Any], Subscription)

  private[instrument] sealed abstract class Command

  private[instrument] case class Behave(
    channel: ScriptedChannel[Any],
    start: mutable.Map[ScriptedChannel[Any], Behavior] => Behavior
  ) extends Command

  private[instrument] case class Deliver(
    channel: ScriptedChannel[Any], url: ChannelUrl, event: Any
  ) extends Command

  private[instrument] case class Clear() extends Command

  private[instrument] class ScriptedChannel[@spec(Int, Long, Double) T](
    val transport: ScriptedTransport, val url: ChannelUrl
  ) extends Channel[T] {
    def send(x: T): Unit = {
      val undermux = transport.multiplexer.asInstanceOf[Channel.Shared[T]].underlying
      if (this eq undermux) {
        transport.system.channels.getLocal[T](url).get ! x
      } else {
        val deliver = Deliver(
          this.asInstanceOf[ScriptedChannel[Any]],
          url,
          x.asInstanceOf[Any]
        )
        transport.multiplexer ! deliver
      }
    }
  }
}


class ScriptedMultiplexer
extends Reactor[ScriptedTransport.Command] {
  import ScriptedTransport._

  private[instrument] val channelBehaviors =
    mutable.Map[ScriptedChannel[Any], Behavior]()

  main.events onMatch {
    case Behave(channel, start) =>
      channelBehaviors(channel) = start(channelBehaviors)
    case Deliver(channel, url, event) =>
      channelBehaviors.get(channel.asInstanceOf[ScriptedChannel[Any]]) match {
        case Some((emitter, sub)) =>
          emitter.asInstanceOf[Events.Emitter[Any]].react(event)
        case None =>
          val isoName = url.reactorUrl.name
          val chName = url.anchor
          system.channels.getLocal[Any](isoName, chName) match {
            case Some(ch) => ch ! event
            case None =>
          }
      }
    case Clear() =>
      main.seal()
      channelBehaviors.clear()
  }
}
