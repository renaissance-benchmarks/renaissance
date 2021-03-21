package io.reactors
package services



import io.reactors.common.IndexMap
import io.reactors.concurrent.Frame
import io.reactors.concurrent.Services
import java.util.Timer
import java.util.TimerTask
import java.util.concurrent.atomic._
import scala.annotation.tailrec
import scala.annotation.unchecked
import scala.collection._
import scala.concurrent.duration._
import scala.reflect.ClassTag



/** Contains services needed to communicate with the debugger.
 */
class Debugger(val system: ReactorSystem) extends Protocol.Service {
  object terminal {
    val log = (x: Any) => system.debugApi.log(Services.loggingTag() + x)
  }

  def shutdown() {}
}


/** Contains various logging-related services.
 */
class Log(val system: ReactorSystem) extends Protocol.Service {
  val apply = (x: Any) => System.out.println(Services.loggingTag() + x.toString)

  def shutdown() {}
}


class NameResolverReactor
extends Reactor[(String, Channel[Option[Channel[_]]])] {
  main.events onMatch {
    case (name, answer) => answer ! system.channels.get(name)
  }
}


class NameAwaiterReactor
extends Reactor[(String, Channel[Channel[_]])] {
  main.events onMatch {
    case (name, answer) =>
      system.channels.await(name).onEvent((ch: Channel[_]) => answer ! ch)
  }
}


/** Contains name resolution reactors.
 */
class Names(val system: ReactorSystem) extends Protocol.Service {
  /** Immediately replies to channel lookup requests.
   */
  lazy val resolve: Channel[(String, Channel[Option[Channel[_]]])] = {
    val p = Proto[NameResolverReactor]
      .withName("~names/resolve")
      .withChannelName("channel")
    system.spawn(p)
  }

  /** Eventually replies to a channel lookup request, when the channel appears.
   */
  lazy val await: Channel[(String, Channel[Channel[_]])] = {
    val p = Proto[NameAwaiterReactor]
      .withName("~names/await")
      .withChannelName("channel")
    system.spawn(p)
  }

  def shutdown() {
  }
}


/** Contains various time-related services.
 */
class Clock(val system: ReactorSystem) extends Protocol.Service {
  private val timer = new Timer(s"reactors-io.${system.name}.timer-service", true)

  def shutdown() {
    timer.cancel()
  }

  /** Emits an event periodically, with the duration between events equal to `d`.
   *
   *  Note that these events are fired eventually, and have similar semantics as that
   *  of fixed-delay execution in `java.util.Timer`.
   *
   *  The channel through which the events arrive is a daemon.
   *
   *  @param d        duration between events
   *  @return         a signal with the index of the event
   */
  def periodic(d: Duration): Signal[Long] = {
    val connector = system.channels.daemon.open[Long]
    val task = new TimerTask {
      var i = 0L
      def run() {
        i += 1
        connector.channel ! i
      }
    }
    timer.schedule(task, d.toMillis, d.toMillis)
    val sub = new Subscription {
      def unsubscribe() {
        task.cancel()
        connector.seal()
      }
    }
    connector.events.toSignal(0L).withSubscription(sub)
  }

  /** Emits an event after a timeout specified by the duration `d`.
   *
   *  Note that this event is fired eventually after duration `d`, and has similar
   *  semantics as that of `java.util.Timer`.
   *
   *  The channel through which the event arrives is daemon.
   *
   *  @param d        duration after which the timeout event fires
   *  @return         a signal that emits the event on timeout
   */
  def timeout(d: Duration): IVar[Unit] = {
    val connector = system.channels.daemon.open[Unit]
    val task = new TimerTask {
      def run() {
        connector.channel ! (())
      }
    }
    timer.schedule(task, d.toMillis)
    val ivar = connector.events.toIVar
    ivar.onDone {
      task.cancel()
      connector.seal()
    }
    ivar
  }

  /** Emits an event at regular intervals, until the specified count reaches zero.
   *
   *  Note that this event is fired eventually after duration `d`, and has similar
   *  semantics as that of `java.util.Timer`.
   *
   *  The channel through which the event arrives is daemon.
   *
   *  Once the countdown reaches `0`, the resulting event stream unreacts, and the
   *  channel is sealed.
   *
   *  @param n        the starting value of the countdown
   *  @param d        period between countdowns
   *  @return         a signal with the countdown events
   */
  def countdown(n: Int, d: Duration): Signal[Int] = {
    assert(n > 0)
    val connector = system.channels.daemon.open[Int]
    val task = new TimerTask {
      var left = n
      def run() = if (left > 0) {
        left -= 1
        connector.channel ! left
      }
    }
    timer.schedule(task, d.toMillis, d.toMillis)
    val sub = Subscription {
      task.cancel()
      connector.seal()
    }
    val signal = connector.events.dropAfter(_ == 0).toSignal(n).withSubscription(sub)
    signal.ignoreExceptions.onDone(sub.unsubscribe())
    signal
  }
}


/** The channel register used for channel lookup by name, and creating new channels.
 *
 *  It can be used to query the channels in the local reactor system.
 *  To query channels in remote reactor systems, `Names` service should be used.
 */
class Channels(val system: ReactorSystem)
extends ChannelBuilder(
  null, false, EventQueue.UnrolledRing.Factory, false, immutable.Map()
) with Protocol.Service {
  private val tagMap = new IndexMap[Channels.Tag, ChannelBuilder]

  def shutdown() {
  }

  private[reactors] def getConnector[T](
    reactorName: String, channelName: String
  ): Option[Connector[T]] = {
    val info = system.frames.forName(reactorName)
    if (info == null) None
    else {
      info.connectors.get(channelName) match {
        case Some(conn: Connector[T] @unchecked) => Some(conn)
        case _ => None
      }
    }
  }

  private[reactors] def getLocal[T](
    reactorName: String, channelName: String
  ): Option[Channel[T]] = {
    getConnector[T](reactorName, channelName).map(_.localChannel)
  }

  private[reactors] def getLocal[T](url: ChannelUrl): Option[Channel[T]] = {
    getLocal[T](url.reactorUrl.name, url.anchor)
  }

  /** Registers a channel builder template under a specific tag.
   *
   *  Specific protocols use channel builder templates to instantiate their components,
   *  and overriding a template in some cases allows to inject custom behavior (for
   *  example, for testing purposes).
   *  Removes previous registrations, if any.
   */
  def registerTemplate(tag: Channels.Tag, template: ChannelBuilder): Unit =
    system.monitor.synchronized {
      tagMap(tag) = template
    }

  /** Returns a channel builder template that had been previously registered for a tag.
   *
   *  If no template was registered with the specified tag, method returns `this`.
   */
  def template(tag: Channels.Tag): ChannelBuilder = system.monitor.synchronized {
    val v = tagMap(tag)
    if (v != null) v
    else this
  }

  /** Optionally returns the channel with the given name, if it exists.
   *
   *  @param name      names of the reactor and the channel, separated with a `#`
   */
  def get[T](name: String): Option[Channel[T]] = {
    val parts = name.split("#")
    if (parts.length != 2)
      exception.illegalArg("Channel name must contain exactly one '#'.")
    else get[T](parts(0), parts(1))
  }

  /** Optionally returns the channel with the given name, if it exists.
   *
   *  @param reactorName  name of the reactor
   *  @param channelName  name of the channel
   */
  def get[T](reactorName: String, channelName: String): Option[Channel[T]] = {
    getConnector[T](reactorName, channelName).map(_.channel)
  }

  /** Await for the channel with the specified full name.
   *
   *  @param name         name of the reactor and the channel, delimited with a `#`
   *  @return             `Ivar` with the desired channel
   */
  final def await[T](name: String): IVar[Channel[T]] = {
    val parts = name.split("#")
    if (parts.length != 2)
      exception.illegalArg("Channel name must contain exactly one '#'.")
    else await[T](parts(0), parts(1))
  }

  /** Await for the channel of the specific reactor, and a specific name.
   *
   *  @param reactorName  name of the reactor
   *  @param channelName  name of the channel
   *  @return             `IVar` with the desired channel
   */
  final def await[T](
    reactorName: String, channelName: String
  ): IVar[Channel[T]] = {
    assert(reactorName != null)
    val conn = system.channels.daemon.open[Channel[T]]
    val ivar = conn.events.toIVar
    ivar.on(conn.seal())

    @tailrec def retry() {
      val info = system.frames.forName(reactorName)
      if (info == null) {
        val ninfo = Frame.Info(null, immutable.Map(channelName -> List(conn.channel)))
        if (system.frames.tryStore(reactorName, ninfo) == null) retry()
      } else {
        info.connectors.get(channelName) match {
          case Some(c: Connector[T] @unchecked) =>
            ivar := c.channel
          case Some(lst: List[Channel[Channel[T]]] @unchecked) =>
            val nchs = channelName -> (conn.channel :: lst)
            val ninfo = Frame.Info(info.frame, info.connectors + nchs)
            if (!system.frames.tryReplace(reactorName, info, ninfo)) retry()
          case None =>
            val nchs = channelName -> List(conn.channel)
            val ninfo = Frame.Info(info.frame, info.connectors + nchs)
            if (!system.frames.tryReplace(reactorName, info, ninfo)) retry()
          case v =>
            exception.illegalState("Should not reach this: " + v)
        }
      }
    }
    retry()

    ivar
  }
}


object Channels {
  abstract class Tag extends IndexMap.Key
}
