package io.reactors
package protocol



import io.reactors.common.ArrayRing
import io.reactors.common.BinaryHeap
import io.reactors.common.UnrolledRing
import io.reactors.services.Channels
import scala.concurrent.duration._



/** Reliable communication protocols ensure reliable delivery.
 *
 *  Reliable delivery is normally ensured when delivering events between reactors
 *  in the same reactor system. However, when the underlying transport is an unreliable
 *  network, events may be delayed, lost, duplicated or arbitrarily corrupted,
 *  depending on the properties of the communication medium.
 *
 *  Reliability protocols ensure that all original events are delivered exactly once
 *  and in order, using either one-way or two-way reliable links.
 */
trait ReliableProtocols {
  /** Represents a connected reliable channel.
   *
   *  When using a reliable channel to send events, clients have some level of guarantee
   *  that their events will not be impaired in some way. The exact guarantees are
   *  detailed in the `Policy` object which must be specified when establishing a
   *  reliable link.
   *
   *  To close this reliable link, clients must use the associated subscription.
   *
   *  @tparam T                 type of the events sent by this reliable channel
   *  @param channel            channel underlying the reliable link
   *  @param subscription       subscription associated with the reliable link
   */
  case class Reliable[T](channel: Channel[T], subscription: Subscription)

  object Reliable {
    /** Represents the reading side of a reliable link.
     *
     *  @tparam T               type of the events incoming on this reliable link
     *  @param events           event stream for incoming events of this link
     *  @param subscription     subscription of the link
     */
    case class Link[T](events: Events[T], subscription: Subscription)
    extends io.reactors.protocol.Connection[T]

    /** State of the reliable channel server.
     *
     *  @tparam T               type of the events in the incoming links
     *  @param channel          channel used to request reliable links
     *  @param links            event stream of established links
     *  @param subscription     subscription of the server
     */
    case class Server[T](
      channel: Channel[Req[T]],
      links: Events[Reliable.Link[T]],
      subscription: Subscription
    ) extends ServerSide[Req[T], Reliable.Link[T]]

    /** Type of the requests for establishing reliable channels.
     *
     *  @tparam T               type of events propagated through reliable channels
     */
    type Req[T] = io.reactors.protocol.TwoWay.Req[Long, Stamp[T]]

    /** Captures the assumptions about the lossiness of the underlying transport.
     *
     *  Depending on the lossiness assumptions, different policies must be used
     *  to establish reliability.
     */
    trait Policy {
      /** Wires client-sent events to the two-way link.
       */
      def client[T: Arrayable](
        sends: Events[T],
        twoWay: io.reactors.protocol.TwoWay[Long, Stamp[T]]
      ): Subscription

      /** Wires the two-way link to the delivery channel of the server.
       */
      def server[T: Arrayable](
        twoWay: io.reactors.protocol.TwoWay[Stamp[T], Long],
        deliver: Channel[T]
      ): Subscription
    }

    object Policy {
      /** Assumes that the transport may reorder and indefinitely delay some events.
       *
       *  Furthermore, the requirement is that the underlying medium is not lossy,
       *  and that it does not create duplicates.
       *
       *  This policy also takes care not to overflow the receiver by buffering events
       *  at the sender if necessary.
       *
       *  @param window     number of events that the policy will send without an
       *                    acknowledgement, before starting to buffer events locally
       */
      def reorder(window: Int) = new Reorder(window)

      /** Same as `reorder`, but faster.
       *
       *  This policy does not take care to avoid overflowing the receiver.
       */
      def fastReorder = new FastReorder

      /** See `reorder`.
       */
      class Reorder(val window: Int) extends Reliable.Policy {
        def client[T: Arrayable](
          sends: Events[T],
          twoWay: io.reactors.protocol.TwoWay[Long, Stamp[T]]
        ): Subscription = {
          var lastAck = 0L
          var lastStamp = 0L
          val queue = new UnrolledRing[T]
          val io.reactors.protocol.TwoWay(channel, acks, subscription) = twoWay
          sends onEvent { x =>
            if ((lastStamp - lastAck) < window) {
              lastStamp += 1
              channel ! new Stamp.Some(x, lastStamp)
            } else {
              queue.enqueue(x)
            }
          }
          acks onEvent { timestamp =>
            lastAck = math.max(lastAck, timestamp)
            while (queue.nonEmpty && (lastStamp - lastAck) < window) {
              lastStamp += 1
              channel ! new Stamp.Some(queue.dequeue(), lastStamp)
            }
          } andThen (channel ! Stamp.None())
        }

        def server[T: Arrayable](
          twoWay: io.reactors.protocol.TwoWay[Stamp[T], Long],
          deliver: Channel[T]
        ): Subscription = {
          val io.reactors.protocol.TwoWay(acks, events, subscription) = twoWay
          var nextStamp = 1L
          val queue = new BinaryHeap[Stamp[T]]()(
            implicitly, Order((x, y) => (x.stamp - y.stamp).toInt)
          )
          var mustSendAck = false
          val ackSub = Reactor.self.sysEvents onMatch { case ReactorPreempted =>
            if (mustSendAck) {
              acks ! (nextStamp - 1)
              mustSendAck = false
            }
          }
          events onMatch {
            case stamp @ Stamp.Some(x, timestamp) =>
              if (timestamp == nextStamp) {
                nextStamp += 1
                deliver ! x
                while (queue.nonEmpty && queue.head.stamp == nextStamp) {
                  val Stamp.Some(y, _) = queue.dequeue()
                  nextStamp += 1
                  deliver ! y
                }
                mustSendAck = true
              } else {
                queue.enqueue(stamp)
              }
          } chain (ackSub) andThen (acks ! -1)
        }
      }

      /** See `fastReorder`.
       */
      class FastReorder extends Reliable.Policy {
        def client[T: Arrayable](
          sends: Events[T],
          twoWay: io.reactors.protocol.TwoWay[Long, Stamp[T]]
        ): Subscription = {
          var lastStamp = 0L
          val io.reactors.protocol.TwoWay(channel, acks, subscription) = twoWay
          sends onEvent { x =>
            lastStamp += 1
            channel ! new Stamp.Some(x, lastStamp)
          }
        }

        def server[T: Arrayable](
          twoWay: io.reactors.protocol.TwoWay[Stamp[T], Long],
          deliver: Channel[T]
        ): Subscription = {
          val io.reactors.protocol.TwoWay(acks, events, subscription) = twoWay
          var nextStamp = 1L
          val queue = new io.reactors.common.BinaryHeap[Stamp[T]]()(
            implicitly, Order((x, y) => (x.stamp - y.stamp).toInt)
          )
          events onMatch {
            case stamp @ Stamp.Some(x, timestamp) =>
              if (timestamp == nextStamp) {
                nextStamp += 1
                deliver ! x
                while (queue.nonEmpty && queue.head.stamp == nextStamp) {
                  val Stamp.Some(y, _) = queue.dequeue()
                  nextStamp += 1
                  deliver ! y
                }
              } else {
                queue.enqueue(stamp)
              }
          } andThen (acks ! -1)
        }
      }
    }

    object TwoWay {
      /** State of the reliable two-way channel server.
       *
       * @tparam I               incoming event type, from the client's perspective
       * @tparam O               outgoing event type, from the client's perspective
       * @param channel          channel used to establish a reliable two-way link
       * @param links            event stream that emits established links
       * @param subscription     subscription of the server
       */
      case class Server[I, O](
        channel: io.reactors.protocol.Server[
          Channel[Reliable.Req[I]],
          Channel[Reliable.Req[O]]
        ],
        links: Events[TwoWay[O, I]],
        subscription: Subscription
      ) extends ServerSide[TwoWay.Req[I, O], TwoWay[O, I]]

      /** Type of the request used to establish reliable two-way links.
       *
       *  @tparam I          type of the incoming events, from the client's perspective
       *  @tparam O          type of the outgoing events, from the client's perspective
       */
      type Req[I, O] = io.reactors.protocol.Server.Req[
        Channel[Reliable.Req[I]],
        Channel[Reliable.Req[O]]
      ]

      /** Captures the assumption about the lossiness of the underlying transport.
       *
       *  Depending on the lossiness of the transport, different policies must be
       *  used when establishing a reliable two-way link.
       */
      trait Policy extends Reliable.Policy {
        /** Guard placed on the input server after it is created.
         *
         *  This can be used to, for example, add a timeout before closing the server.
         */
        def inputServerGuard[I](inServer: Reliable.Server[I]): Subscription

        /** Guard placed on the output server after it is created.
         *
         *  This can be used to, for example, add a timeout before closing the server.
         */
        def outputServerGuard[O](outServer: Reliable.Server[O]): Subscription
      }

      object Policy {
        trait NoGuard extends Reliable.TwoWay.Policy  {
          def inputServerGuard[I](inServer: Reliable.Server[I]) = Subscription.empty
          def outputServerGuard[I](outServer: Reliable.Server[I]) = Subscription.empty
        }

        /** Policy that assumes that the transport may arbitrarily delay any event.
         *
         *  Additionally, this policy assumes that the transport may reorder events,
         *  but will never drop, duplicate or corrupt the events.
         */
        def reorder(window: Int) =
          new Reliable.Policy.Reorder(window) with Reliable.TwoWay.Policy.NoGuard

        /** Same as reorder, but faster.
         */
        def fastReorder =
          new Reliable.Policy.FastReorder with Reliable.TwoWay.Policy.NoGuard
      }
    }

    /** Tags the channel of the `Reliable` object.
     */
    object ChannelTag extends Channels.Tag
  }

  /* One-way reliable protocols */

  implicit class ReliableChannelBuilderOps(val builder: ChannelBuilder) {
    /** Opens a connector for a reliable link server.
     *
     *  Note that opening a connector does not yet start the protocol.
     *  To start the reliable channel server, `serveReliable` must be called
     *  on the connector.
     *
     *  @tparam T        type of the events of the established reliable links
     *  @return          a connector for the reliable link server
     */
    def reliableServer[T]: Connector[Reliable.Req[T]] = {
      builder.open[Reliable.Req[T]]
    }
  }

  implicit class ReliableConnectorOps[T: Arrayable](
    val connector: Connector[Reliable.Req[T]]
  ) {
    /** Starts a server that responds to incoming requests for reliable links.
     *
     *  @param policy     captures assumptions about the underlying transport
     *  @return           state of the new reliable links server
     */
    def serveReliable(
      policy: Reliable.Policy = Reliable.Policy.reorder(128)
    ): Reliable.Server[T] = {
      import scala.language.postfixOps

      val system = Reactor.self.system
      val twoWayServer = connector.serveTwoWay()
      val links = twoWayServer.links map {
        case twoWay @ TwoWay(_, events, _) =>
          val reliable =
            system.channels.template(Reliable.ChannelTag).daemon.shortcut.open[T]
          val resources = policy.server(twoWay, reliable.channel)
          val subscription = Subscription(reliable.seal())
            .chain(resources)
            .chain(twoWay.subscription)
          events.collect({ case s @ Stamp.None() => s })
            .toIVar.on(subscription.unsubscribe())
          Reliable.Link(reliable.events, subscription)
      } toEmpty

      Reliable.Server(
        connector.channel,
        links,
        links.chain(twoWayServer.subscription).andThen(connector.seal())
      )
    }
  }

  implicit class ReliableServerOps[T: Arrayable](
    val server: Channel[Reliable.Req[T]]
  ) {
    /** Opens a reliable link.
     *
     *  @param policy      captures assumption about the underlying transport
     *  @return            single-assignment variable that is eventually completed with
     *                     the reliable link object
     */
    def openReliable(
      policy: Reliable.Policy = Reliable.Policy.reorder(128)
    ): IVar[Reliable[T]] = {
      import scala.language.postfixOps

      val system = Reactor.self.system
      server.connect() map {
        case twoWay @ TwoWay(_, acks, _) =>
          val reliable = system.channels.daemon.shortcut.open[T]
          val resources = policy.client(reliable.events, twoWay)
          val subscription = Subscription(reliable.seal())
            .chain(resources)
            .chain(twoWay.subscription)
          acks.filter(_ == -1).toIVar.on(subscription.unsubscribe())
          Reliable(reliable.channel, subscription)
      } toIVar
    }
  }

  implicit class ReliableReactorCompanionOps(val reactor: Reactor.type) {
    /** Same as calling the `serveReliable` operation, but creates a `Proto` object.
     */
    def reliableServer[T: Arrayable](policy: Reliable.Policy)(
      f: Reliable.Server[T] => Unit
    ): Proto[Reactor[Reliable.Req[T]]] = {
      Reactor[Reliable.Req[T]] { self =>
        val server = self.main.serveReliable(policy)
        f(server)
      }
    }
  }

  implicit class ReliableSystemOps(val system: ReactorSystem) {
    /** Same as calling the `serveReliable` operation, but starts the reactor directly.
     */
    def reliableServer[T: Arrayable](policy: Reliable.Policy)(
      f: Reliable.Server[T] => Unit
    ): Channel[Reliable.Req[T]] = {
      system.spawn(Reactor.reliableServer[T](policy)(f))
    }
  }

  /* Two-way reliable protocols */

  implicit class ReliableTwoWayChannelBuilderOps(val builder: ChannelBuilder) {
    /** Opens a connector that can accept requests for reliable two-way links.
     *
     *  Does not start the reliable two-way server protocol. For that, clients must
     *  call the `serverTwoWayReliable` method on the connector.
     *
     *  @tparam I      type of the incoming events, from the client's perspective
     *  @tparam O      type of the outgoing events, from the client's perspective
     *  @return        a newly created connector for the reliable two-way requests
     */
    def reliableTwoWayServer[I, O]: Connector[Reliable.TwoWay.Req[I, O]] = {
      builder.open[Reliable.TwoWay.Req[I, O]]
    }
  }

  implicit class ReliableTwoWayConnectorOps[I: Arrayable, O: Arrayable](
    val connector: Connector[Reliable.TwoWay.Req[I, O]]
  ) {
    /** Starts a server that accepts requests for two-way reliable links.
     *
     *  @param policy  captures assumptions about the underlying transport
     *  @return        state of the newly created two-way reliable server
     */
    def serveTwoWayReliable(
      policy: Reliable.TwoWay.Policy = Reliable.TwoWay.Policy.reorder(128)
    ): Reliable.TwoWay.Server[I, O] = {
      val system = Reactor.self.system
      val links = connector.events.map {
        case req @ (inServer, reply) =>
          val outServer = system.channels.daemon.shortcut.reliableServer[O]
            .serveReliable(policy)
          outServer.links.on(outServer.subscription.unsubscribe())
          policy.outputServerGuard(outServer)
          reply ! outServer.channel

          val inReliable = inServer.openReliable(policy)

          (outServer.links sync inReliable) { (out, in) =>
            TwoWay(in.channel, out.events, in.subscription.chain(out.subscription))
          } toIVar
      }.union.toEmpty

      Reliable.TwoWay.Server(
        connector.channel,
        links,
        links.andThen(connector.seal())
      )
    }
  }

  implicit class ReliableTwoWayServerOps[I: Arrayable, O: Arrayable](
    val reliableServer: Channel[io.reactors.protocol.Reliable.TwoWay.Req[I, O]]
  ) {
    /** Requests and establishes a two-way reliable link.
     *
     *  @param policy    captures assumptions about the underlying transport
     *  @return          a single-assignment variable with the established two-way
     *                   link, completed once the link is established
     */
    def connectReliable(
      policy: Reliable.TwoWay.Policy = Reliable.TwoWay.Policy.reorder(128)
    ): IVar[TwoWay[I, O]] = {
      val system = Reactor.self.system
      val inServer = system.channels.daemon.shortcut.reliableServer[I]
        .serveReliable(policy)
      policy.inputServerGuard(inServer)
      inServer.links.on(inServer.subscription.unsubscribe())

      (reliableServer ? inServer.channel).map { outServer =>
        val outReliable = outServer.openReliable(policy)

        (outReliable sync inServer.links) { (out, in) =>
          TwoWay(out.channel, in.events, out.subscription.chain(in.subscription))
        }
      }.union.toIVar
    }
  }

  implicit class ReliableTwoWayReactorCompanionOps(val reactor: Reactor.type) {
    /** Same as `serveTwoWayReliable`, but creates a `Proto` object.
     *
     *  The reactor's main channel is used as the two-way reliable link server.
     */
    def reliableTwoWayServer[I: Arrayable, O: Arrayable](
      policy: Reliable.TwoWay.Policy
    )(
      f: Reliable.TwoWay.Server[I, O] => Unit
    ): Proto[Reactor[Reliable.TwoWay.Req[I, O]]] = {
      Reactor[Reliable.TwoWay.Req[I, O]] { self =>
        val server = self.main.serveTwoWayReliable(policy)
        f(server)
      }
    }
  }

  implicit class ReliableTwoWaySystemOps[I: Arrayable, O: Arrayable](
    val system: ReactorSystem
  ) {
    /** Same as `serveTwoWayReliable`, but immediately starts the reactor.
     *
     *  The reactor's main channel is used as the two-way reliable link server.
     */
    def reliableTwoWayServer(policy: Reliable.TwoWay.Policy)(
      f: Reliable.TwoWay.Server[I, O] => Unit
    ): Channel[Reliable.TwoWay.Req[I, O]] = {
      val proto = Reactor.reliableTwoWayServer(policy)(f)
      system.spawn(proto)
    }
  }
}
