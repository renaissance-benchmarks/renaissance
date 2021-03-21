package io.reactors



import scala.collection._
import scala.reflect.ClassTag



/** Used for building channel objects.
 */
class ChannelBuilder(
  val channelName: String,
  val isDaemon: Boolean,
  val eventQueueFactory: EventQueue.Factory,
  val shortcutLocal: Boolean,
  private val extras: immutable.Map[Class[_], Any]
) {
  /** Associates a new name for the channel.
   */
  def named(name: String) =
    new ChannelBuilder(name, isDaemon, eventQueueFactory, shortcutLocal, extras)

  /** Designates whether this channel can bypass the event queue for local sends.
   *
   *  This is `false` by default.
   */
  def shortcut =
    new ChannelBuilder(channelName, isDaemon, eventQueueFactory, true, extras)

  /** Specifies a daemon channel.
   */
  def daemon =
    new ChannelBuilder(channelName, true, eventQueueFactory, shortcutLocal, extras)

  /** Specifies a daemon channel.
   */
  def nonDaemon =
    new ChannelBuilder(channelName, false, eventQueueFactory, shortcutLocal, extras)

  /** Associates a new event queue factory.
   */
  def eventQueue(factory: EventQueue.Factory) =
    new ChannelBuilder(channelName, isDaemon, factory, shortcutLocal, extras)

  /** Associates extra information with the channel being built.
   *
   *  Only one object of the specified class can be stored.
   */
  def extra[C: ClassTag](value: C) = {
    val nextras = extras + (implicitly[ClassTag[C]].runtimeClass -> value)
    new ChannelBuilder(channelName, isDaemon, eventQueueFactory, shortcutLocal, nextras)
  }

  /** Opens a new channel for this reactor.
   *
   *  @tparam Q        type of the events in the new channel
   *  @return          the connector object of the new channel
   */
  final def open[@spec(Int, Long, Double) Q: Arrayable]: Connector[Q] =
    Reactor.self.frame.openConnector[Q](
      channelName, eventQueueFactory, isDaemon, shortcutLocal, extras)
}
