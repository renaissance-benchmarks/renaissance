package io.reactors
package protocol






/** Communication patterns based on request-reply.
 */
trait ServerProtocols {
  /** A server channel accepts tuples with the request event and channel to reply on.
   */
  type Server[T, S] = Channel[Server.Req[T, S]]

  /** Contains various options for tuning the server protocol.
   */
  object Server {
    type Req[T, S] = (T, Channel[S])

    object Stream {
      type Req[T, S] = io.reactors.protocol.Server.Req[(T, S), S]
    }

    case class State[T, S](channel: Server[T, S], subscription: Subscription)
  }

  implicit class ServerChannelBuilderOps(val builder: ChannelBuilder) {
    /** Open a new server channel.
     *
     *  The returned connector only has the server type, but will not serve incoming
     *  requests - for this, `serve` must be called on the connector.
     */
    def server[T, S]: Connector[Server.Req[T, S]] = builder.open[Server.Req[T, S]]

    /** Open a new streaming server channel.
     *
     *  Method `serve` must be subsequently called to start the server.
     */
    def streamServer[T, S]: Connector[Server.Stream.Req[T, S]] =
      builder.open[Server.Stream.Req[T, S]]
  }

  implicit class ServerConnectorOps[T, S](val conn: Connector[Server.Req[T, S]]) {
    /** Installs a serving function to the specified connector.
     */
    def serve(f: T => S): Server.State[T, S] = {
      val sub = conn.events onMatch {
        case (x, ch) => ch ! f(x)
      }
      Server.State(conn.channel, sub.andThen(conn.seal()))
    }

    /** Installs an asynchronous serving function to the specified connector.
     *
     *  Only the first event from the reply event stream is forwarded to the client.
     */
    def asyncServe(f: T => Events[S]): Server.State[T, S] = {
      val sub = conn.events onMatch {
        case (x, ch) => f(x).once.onEvent(y => ch ! y)
      }
      Server.State(conn.channel, sub.andThen(conn.seal()))
    }
  }

  implicit class ServerReactorCompanionOps(val system: Reactor.type) {
    /** Creates a `Proto` object for a server reactor.
     *
     *  The behavior of the server reactor is specified by the function `f`, which maps
     *  input requests to responses.
     */
    def server[T, S](
      f: (Server.State[T, S], T) => S
    ): Proto[Reactor[Server.Req[T, S]]] = {
      Reactor[Server.Req[T, S]] { self =>
        var server: Server.State[T, S] = null
        server = self.main.serve(x => f(server, x))
      }
    }
  }

  implicit class ServerSystemOps(val system: ReactorSystem) {
    /** Creates a server reactor.
     *
     *  This reactor always responds by mapping the request of type `T` into a response
     *  of type `S`, with the specified function `f`.
     */
    def server[T, S](f: (Server.State[T, S], T) => S): Server[T, S] = {
      system.spawn(Reactor.server(f))
    }
  }

  implicit class ServerStreamConnectorOps[T, @specialized(Int, Long, Double) S](
    val conn: Connector[Server.Stream.Req[T, S]]
  ) {
    /** Starts the stream server.
     *
     *  For each streaming request, an event stream is created using the specified
     *  function. Events from this event stream are streamed to the client,
     *  and a terminator value is sent at the end.
     */
    def stream(f: T => Events[S]): Server.State[(T, S), S] = {
      val subscription = conn.events onMatch {
        case ((x, term), ch) => f(x).onEventOrDone(y => ch ! y)(ch ! term)
      }
      Server.State(conn.channel, subscription.andThen(conn.seal()))
    }
  }

  implicit class ServerOps[T, @specialized(Int, Long, Double) S: Arrayable](
    val server: Server[T, S]
  ) {
    /** Request a single reply from the server channel.
     *
     *  Returns an `IVar` with the server response.
     *  If the server responds with multiple events, only the first event is returned.
     *
     *  @param x     request event
     *  @return      the single assignment variable with the reply
     */
    def ?(x: T): IVar[S] = {
      val connector = Reactor.self.system.channels.daemon.open[S]
      val result = connector.events.toIVar
      result.onDone(connector.seal())
      server ! (x, connector.channel)
      result
    }

    /** Send a request to the server, but ignore the response.
     *
     *  @param x     request event
     */
    def ?!(x: T): Unit = server ! (x, new Channel.Zero[S])
  }

  implicit class ServerStreamOps[T, @specialized(Int, Long, Double) S: Arrayable](
    val server: Server[(T, S), S]
  ) {
    /** Request a stream of replies from the server channel.
     *
     *  The stream is interrupted when the server sends a `term` event.
     *
     *  Server can reply with multiple events.
     *  There is no backpressure in this algorithm, so clients are responsible for
     *  ensuring that the server does not flood the client.
     *  Furthermote, the client can at any point unsubscribe from the event
     *  stream without notifying the server, so ensuring that the server sends a finite
     *  stream is strongly recommended.
     *
     *  @param x     request event
     *  @param term  termination event, server must use it to indicate the end of stream
     *  @return      a signal emitting the server replies
     */
    def askStream(x: T, term: S): Signal[S] = {
      val connector = Reactor.self.system.channels.open[S]
      val result = connector.events.takeWhile(_ != term).toEmpty
      result.onDone(connector.seal())
      server ! ((x, term), connector.channel)
      result.withSubscription(Subscription { connector.seal() })
    }
  }
}
