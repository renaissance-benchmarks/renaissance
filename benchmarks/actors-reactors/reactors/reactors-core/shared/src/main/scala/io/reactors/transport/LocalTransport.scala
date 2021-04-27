package io.reactors.transport



import io.reactors._



/** Delivers locally, to reactors within the current reactor system.
 *
 *  This is usually the default transport in the reactor system, but it is only
 *  used with newly created channels when the configuration option
 *  `system.channels.create-as-local` is set to `"false"`.
 *  Otherwise, local channels use a fast, direct delivery mode, which bypasses
 *  the transport layer.
 */
class LocalTransport(val system: ReactorSystem) extends Remote.Transport {
  def schema = "local"

  def port = -1

  def newChannel[@spec(Int, Long, Double) T: Arrayable](url: ChannelUrl): Channel[T] = {
    new LocalTransport.LocalChannel(this, url)
  }

  override def shutdown(): Unit = {
  }
}


object LocalTransport {
  private[transport] class LocalChannel[@spec(Int, Long, Double) T](
    val transport: LocalTransport, val url: ChannelUrl
  ) extends Channel[T] {
    def send(x: T): Unit = {
      val isoName = url.reactorUrl.name
      val chName = url.anchor
      transport.system.channels.getLocal[T](isoName, chName) match {
        case Some(ch) => ch ! x
        case None =>
      }
    }
  }
}
