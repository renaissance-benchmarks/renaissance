package io.reactors



import scala.collection._



/** Service that tracks different transports for remote communication.
 *
 *  The most important method is `resolve`, which creates a channel from a
 *  channel URL. This allows communication with reactors in non-local
 *  reactor systems, e.g. in another process, or on another machine.
 */
class Remote(val system: ReactorSystem) extends Protocol.Service {
  private val transports = mutable.Map[String, Remote.Transport]()

  private def initializeTransport(schema: String): Unit = {
    val t = system.bundle.urlMap(schema)
    val transport = Platform.Reflect.instantiate(t.transportName, Seq(system))
      .asInstanceOf[Remote.Transport]
    if (transport.schema != t.url.schema) exception.illegalArg(
      s"Transport with schema '${transport.schema}' must have the same schema in " +
      s"the reactor system configuration."
    )
    transports(t.url.schema) = transport
  }

  def transport(schema: String) = {
    if (!transports.contains(schema)) {
      initializeTransport(schema)
    }
    transports(schema)
  }

  def resolve[@spec(Int, Long, Double) T: Arrayable](url: ChannelUrl): Channel[T] = {
    val schema = url.reactorUrl.systemUrl.schema
    if (!transports.contains(schema)) {
      initializeTransport(schema)
    }
    transports(schema).newChannel[T](url)
  }

  def resolve[@spec(Int, Long, Double) T: Arrayable](url: String): Channel[T] = {
    val channelUrl = ChannelUrl.parse(url)
    resolve(channelUrl)
  }

  def shutdown() {
    for ((schema, transport) <- transports) transport.shutdown()
  }
}


/** Types and methods related to the `Remote` service.
 */
object Remote {
  /** Interface for the transport API.
   *
   *  Concrete implementations of this interface represent different transports.
   */
  trait Transport extends Platform.Reflectable {
    /** Creates a new channel for this transport.
     *
     *  @tparam T       type of the events for the new channel
     *  @param url      url of the newly created channel
     *  @return         a new channel associated with this transport
     */
    def newChannel[@spec(Int, Long, Double) T: Arrayable](url: ChannelUrl): Channel[T]

    /** The schema string that this transport must be registered with.
     */
    def schema: String

    /** Port associated with the transport if applicable, or `-1` otherwise.
     */
    def port: Int

    /** Shuts down the transport, and releases the associated resources.
     */
    def shutdown(): Unit
  }
}
