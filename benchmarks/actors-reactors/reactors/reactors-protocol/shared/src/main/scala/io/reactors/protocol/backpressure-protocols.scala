package io.reactors
package protocol






/** Backpressure protocols ensure that fast producers do not overwhelm consumers.
 *
 *  In an asynchronous system, there is always a possibility that a producer reactor
 *  sends more events than the consumer can handle. This can eventually blow up the
 *  memory requirements of the consumer, since its event queue grows indefinitely.
 *  Backpressure links ensure that the
 *
 *  Backpressure is parametric in the choice of the underlying communication medium.
 *  A backpressure link is established on top of a two-way link,
 *  but that two-way links may be non-reliable or reliable. This is abstracted
 *  away in a configuration object called a `Medium`, which is necessary to start
 *  the backpressure protocol.
 */
trait BackpressureProtocols {
  object Backpressure {
    /** Represents an established backpressure link.
     *
     *  Connection clients must manually release events from the associated event buffer
     *  and then send pressure tokens back to the producer. The event buffer has an
     *  `available` signal used to notify about event availability.
     *
     *  For convenience, every backpressure link can be converted into a `Pump`
     *  object, which automatically sends backpressure tokens when events are dequeued
     *  from the event buffer.
     *
     *  @tparam T             type of the events delivered on the backpressure channel
     *  @param pressure       backpressure channel, used by consumers to signal the
     *                        producers when additional events can be sent
     *  @param buffer         event buffer that holds events ready to be delivered
     *  @param subscription   resources associated with the link
     */
    case class Link[T](
      pressure: Channel[Int],
      buffer: EventBuffer[T],
      subscription: Subscription
    ) {
      /** Converts this link into a backpressure pump.
       */
      def toPump: Pump[T] = {
        val pressureSubscription = buffer.on(pressure ! 1)
        Pump(
          buffer,
          pressureSubscription.chain(subscription)
        )
      }
    }

    /** Represents the state of a backpressure link server.
     *
     *  @tparam R             type of the request object used by the underlying medium
     *  @tparam T             type of the events delivered on the backpressure channel
     *  @param channel        request channel that allows the clients to send requests
     *                        for new backpressure links
     *  @param links          server-side event stream that emits links that are
     *                        established with this backpressure server
     *  @param subscription   resources associated with the backpressure server
     */
    case class Server[R, T](
      channel: Channel[R],
      links: Events[Link[T]],
      subscription: Subscription
    ) extends ServerSide[R, Link[T]] {
      def toPumpServer: PumpServer[R, T] = {
        new Backpressure.PumpServer(
          channel,
          links.map(_.toPump),
          subscription
        )
      }
    }

    /** A variant of a backpressure server that emits backpressure pumps.
     *
     *  See `Backpressure.Server`.
     */
    case class PumpServer[R, T](
      val channel: Channel[R],
      val links: Events[Pump[T]],
      val subscription: Subscription
    ) extends ServerSide[R, Pump[T]]

    /** Abstracts over the underlying two-way communication protocol.
     *
     *  Captures the protocol needed to create a two-way server, and to connect to it.
     */
    class Medium[R, @spec(Int, Long, Double) T](
      val openServer: ChannelBuilder => Connector[R],
      val serve: Connector[R] => ServerSide[R, TwoWay[T, Int]],
      val connect: Channel[R] => IVar[TwoWay[Int, T]]
    )

    object Medium {
      /** Provides normal non-reliable two-way links.
       */
      def default[@spec(Int, Long, Double) T: Arrayable] =
        new Backpressure.Medium[TwoWay.Req[Int, T], T](
          builder => builder.twoWayServer[Int, T],
          connector => connector.serveTwoWay(),
          channel => channel.connect()
        )

      /** Provides reliable two-way link.
       *
       *  This reliable `Medium` must be parametrized with a reliable two-way policy.
       */
      def reliable[@spec(Int, Long, Double) T: Arrayable](
        policy: Reliable.TwoWay.Policy
      ) = new Backpressure.Medium[Reliable.TwoWay.Req[Int, T], T](
        builder => builder.reliableTwoWayServer[Int, T],
        connector => connector.serveTwoWayReliable(policy),
        channel => channel.connectReliable(policy)
      )
    }

    /** Captures the specific backpressure policy.
     *
     *  While the overall picture with backpressure is that producers can only send
     *  events to consumers once consumers send them pressure tokens,
     *  there are subtle differences in how this backpressure can be implemented.
     *  The details are captured in:
     *  - How the consumer-side (i.e. server-side) pressure stream is forwarded to the
     *    producer.
     *  - How a `Valve` object is created from a two-way link on the
     *    producer-side (i.e. client-side).
     */
    trait Policy {
      def server(
        inPressure: Events[Int], outPressure: Channel[Int]
      ): Subscription
      def client[@spec(Int, Long, Double) T: Arrayable](
        twoWay: TwoWay[Int, T]
      ): Valve[T]
    }

    object Policy {
      private[reactors] def defaultClient[@spec(Int, Long, Double) T: Arrayable](
        size: Int, twoWay: TwoWay[Int, T]
      ): Valve[T] = {
        val system = Reactor.self.system
        val frontend = system.channels.daemon.shortcut.open[T]
        val budget = RCell(0)
        val available = budget.map(_ > 0).toEmpty.changes.toSignal(false)
        val increments = twoWay.input.onEvent(x => budget := budget() + x)
        val forwarding = frontend.events.onEvent { x =>
          if (available()) twoWay.output ! x
          else throw new IllegalStateException("Backpressure channel not available.")
          budget := budget() - 1
        }
        Valve(
          frontend.channel,
          available,
          forwarding.chain(increments).chain(twoWay.subscription)
        )
      }

      /** Consumer sends pressure tokens immediately after processing each input event.
       *
       *  Works well when each input event is large or requires a large amount of
       *  processing.
       *
       *  @param size       maximum number of events that can be sent without additional
       *                    consumer-sent tokens
       */
      def sliding(size: Int) = new Backpressure.Policy {
        def server(inPressure: Events[Int], outPressure: Channel[Int]): Subscription = {
          outPressure ! size
          inPressure onEvent { n =>
            outPressure ! n
          }
        }
        def client[@spec(Int, Long, Double) T: Arrayable](twoWay: TwoWay[Int, T]) =
          defaultClient[T](size, twoWay)
      }

      /** Consumer sends pressure tokens in batches, after getting preempted.
       *
       *  Works well when each input event requires a low amount of processing.
       *
       *  @param size       maximum number of events that cen be sent without additional
       *                    consumer-sent tokens
       */
      def batching(size: Int) = new Backpressure.Policy {
        def server(inPressure: Events[Int], outPressure: Channel[Int]) = {
          outPressure ! size
          val tokens = RCell(0)
          val tokenSubscription = inPressure onEvent { n =>
            tokens := tokens() + n
          }
          val flushSubscription = Reactor.self.sysEvents onMatch {
            case ReactorPreempted =>
              if (tokens() > 0) {
                outPressure ! tokens()
                tokens := 0
              }
          }
          tokenSubscription.chain(flushSubscription)
        }
        def client[@spec(Int, Long, Double) T: Arrayable](twoWay: TwoWay[Int, T]) =
          defaultClient[T](size, twoWay)
      }
    }
  }

  implicit class BackpressureChannelBuilderOps[R, @spec(Int, Long, Double) T](
    val builder: ChannelBuilder
  ) {
    /** Opens a connector for the backpressure server.
     *
     *  This does not start the protocol, use `serveBackpressureConnections` or
     *  `serverBackpressure` for that.
     */
    def backpressureServer(medium: Backpressure.Medium[R, T]): Connector[R] = {
      medium.openServer(builder)
    }
  }

  implicit class BackpressureConnectorOps[R, @spec(Int, Long, Double) T](
    val connector: Connector[R]
  ) {
    /** Starts a server that accepts incoming backpressure link requests.
     *
     *  @param medium        protocol for establishing two-way links
     *  @param policy        captures the details of the backpressure implementation
     *  @return              a backpressure server state object
     */
    def serveBackpressureConnections(
      medium: Backpressure.Medium[R, T],
      policy: Backpressure.Policy
    )(implicit a: Arrayable[T]): Backpressure.Server[R, T] = {
      val twoWayServer = medium.serve(connector)
      Backpressure.Server(
        twoWayServer.channel,
        twoWayServer.links.map {
          case TwoWay(channel, events, twoWaySub) =>
            val system = Reactor.self.system
            val pressure = system.channels.daemon.shortcut.open[Int]
            val sub = policy.server(pressure.events, channel).chain(twoWaySub)
            Backpressure.Link(pressure.channel, events.toEventBuffer, sub)
        },
        twoWayServer.subscription
      )
    }

    /** Starts a server that accepts incoming backpressure pump requests.
     *
     *  See the `Pump` class.
     *
     *  @param medium        protocol for establishing two-way links
     *  @param policy        captures the details of the backpressure implementation
     *  @return              a backpressure server state object
     */
    def serveBackpressure(
      medium: Backpressure.Medium[R, T],
      policy: Backpressure.Policy
    )(implicit a: Arrayable[T]): Backpressure.PumpServer[R, T] = {
      serveBackpressureConnections(medium, policy).toPumpServer
    }
  }

  implicit class BackpressureServerOps[R](val server: Channel[R]) {
    /** Connects to a backpressure server.
     *
     *  @tparam T           type of events delivered on the backpressure link
     *  @param medium       see the `Backpressure.Medium` class
     *  @param policy       see the `Backpressure.Policy` class
     *  @return             a single-assignment variable that is eventually completed
     *                      with the `Valve` object
     */
    def openBackpressure[@spec(Int, Long, Double) T: Arrayable](
      medium: Backpressure.Medium[R, T],
      policy: Backpressure.Policy
    ): IVar[Valve[T]] = {
      medium.connect(server).map(policy.client[T]).toIVar
    }
  }

  implicit class BackpressureReactorCompanionOps(val reactor: Reactor.type) {
    /** Creates a backpressure link server `Proto`.
     *
     *  See `serveBackpressureConnections`.
     */
    def backpressureLinkServer[R: Arrayable, @spec(Int, Long, Double) T: Arrayable](
      medium: Backpressure.Medium[R, T],
      policy: Backpressure.Policy
    )(f: Backpressure.Server[R, T] => Unit): Proto[Reactor[R]] = {
      Reactor[R] { self =>
        f(self.main.serveBackpressureConnections(medium, policy))
      }
    }

    /** Creates a backpressure server `Proto`.
     *
     *  See `serveBackpressure`.
     */
    def backpressureServer[R: Arrayable, @spec(Int, Long, Double) T: Arrayable](
      medium: Backpressure.Medium[R, T],
      policy: Backpressure.Policy
    )(f: Backpressure.PumpServer[R, T] => Unit): Proto[Reactor[R]] = {
      Reactor[R] { self =>
        f(self.main.serveBackpressure(medium, policy))
      }
    }
  }

  implicit class BackpressureSystemOps(val system: ReactorSystem) {
    /** Creates and starts a backpressure link server reactor.
     *
     *  See `serveBackpressureConnections`.
     */
    def backpressureLinkServer[R: Arrayable, @spec(Int, Long, Double) T: Arrayable](
      medium: Backpressure.Medium[R, T],
      policy: Backpressure.Policy
    )(f: Backpressure.Server[R, T] => Unit): Channel[R] = {
      val proto = Reactor.backpressureLinkServer(medium, policy)(f)
      system.spawn(proto)
    }

    /** Creates and starts a backpressure server reactor.
     *
     *  See `serveBackpressure`.
     */
    def backpressureServer[R: Arrayable, @spec(Int, Long, Double) T: Arrayable](
      medium: Backpressure.Medium[R, T],
      policy: Backpressure.Policy
    )(f: Backpressure.PumpServer[R, T] => Unit): Channel[R] = {
      val proto = Reactor.backpressureServer(medium, policy)(f)
      system.spawn(proto)
    }
  }
}
