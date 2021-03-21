/*!md
---
layout: tutorial
title: Two-Way Communication Protocol
topic: reactors
logoname: reactress-mini-logo-flat.png
projectname: Reactors.IO
homepage: http://reactors.io
permalink: /reactors/protocol-two-way/index.html
pagenum: 3
pagetot: 40
section: guide-protocol
---
!*/
package tutorial



import org.scalatest._
import scala.concurrent.ExecutionContext
import scala.concurrent.Promise
import org.scalatest.funsuite.AsyncFunSuite



/*!md
## 2-Way Communication Protocol

In this section, we show a 2-way communication protocol
that is a part of the `reactors-protocol` module.
In 2-way communication,
both the server and the client obtain a link handle of type `TwoWay`,
which allows them to send and receive an unlimited number of events,
until they decide to close this link.
!*/
class GuideTwoWayProtocol extends AsyncFunSuite {

  implicit override def executionContext = ExecutionContext.Implicits.global

  type In = String

  type Out = Int

  /*!md
  In this section, we show a two-way communication protocol.
  In two-way communication, two parties obtain a link handle of type `TwoWay`,
  which allows them to simultaneously send and receive an unlimited number of events,
  until they decide to close this link.
  One party initiates the link, so we call that party the client,
  and the other party the server.
  The `TwoWay` type has two type parameters `I` and `O`,
  which describe the types of input and output events, respectively,
  from the client's point of view.
  Show graphically, this looks as follows:

  ```
   client-side  I <---------- I  server-side
                O ----------> O
  ```

  Note that the types of the `TwoWay` object are reversed
  depending on whether you are looking at the
  link from the server-side or from the client-side.
  The type of the client-side 2-way link is:
  !*/

  trait Foo {
    import io.reactors.protocol._

    /*!begin-code!*/
    val clientTwoWay: TwoWay[In, Out]
    /*!end-code!*/

    /*!md
    Whereas the type of the server would see the 2-way link as:
    !*/

    /*!begin-code!*/
    val serverTwoWay: TwoWay[Out, In]
    /*!end-code!*/

    /*!md
    Accordingly, the `TwoWay` object contains an output channel `output`,
    and an input event stream `input`.
    To close the link, the `TwoWay` object contains a subscription
    object called `subscription`, which is used to close the link
    and free the associated resources.
    !*/
  }

  test("two-way") {
    val done = Promise[String]()
    def println(s: String) = done.success(s)

    /*!md
    Let's instantiate the 2-way channel protocol.
    We start by importing the contents of the `io.reactors`
    and the `io.reactors.protocol` packages,
    and then instantiating a default reactor system.
    !*/

    /*!begin-code!*/
    import io.reactors._
    import io.reactors.protocol._

    val system = ReactorSystem.default("test-system")
    /*!end-code!*/

    /*!md
    The 2-way communication protocol works in two phases.
    First, a client asks a 2-way link server to establish a 2-way link.
    Second, the client and the server use the 2-way channel to communicate.
    Note that a single 2-way link server can create many 2-way links.

    As explained in an earlier section,
    there are usually several ways to instantiate the protocol - either as standalone
    reactor that runs only that protocol, or as a single protocol running inside a
    larger reactor.
    We start with a more general variant. We will declare a reactor,
    and instantiate a 2-way link server within that reactor.
    The 2-way server will receive strings, and respond with the length of those strings.
    !*/

    /*!begin-code!*/
    val seeker = Reactor[Unit] { self =>
      val lengthServer =
        self.system.channels.twoWayServer[Int, String].serveTwoWay()
    /*!end-code!*/

    /*!md
    The above two lines declare a reactor `Proto` object,
    which instantiates a 2-way server called `lengthServer`.
    We did this by first calling the `twoWayServer` method on the `Channels` service,
    and specifying the input and the output type
    (from the point of view of the client).
    We then called `serverTwoWay` to start the protocol.
    In our case, we set the input type `I` to `Int`, meaning that the client will
    receive integers from the server, and the output type `O` to `String`,
    meaning that the client will be sending strings to the server.

    The resulting object `lengthServer` represents the state of the link.
    It contains an event stream called `links`, which emits an event every time
    some client requests a link.
    If we do nothing with this event stream,
    the server will be silent - it will start new links, but ignore events
    incoming from the clients.
    How the client and server communicate over the 2-way channel
    (and when to terminate this communication) is up to the user to specify.
    To customize the 2-way communication protocol with our own logic,
    we need to react to the `TwoWay` events emitted by `links`,
    and install callbacks to the `TwoWay` objects.

    In our case, for each incoming 2-way link,
    we want to react to `input` strings by computing the length of the string
    and then sending that length back along the `output` channel.
    We can do this as follows:
    !*/

    /*!begin-code!*/
      lengthServer.links.onEvent { serverTwoWay =>
        serverTwoWay.input.onEvent { s =>
          serverTwoWay.output ! s.length
        }
      }
    /*!end-code!*/

    /*!md
    So far, so good - we have a working instance of the 2-way link server.
    The current state of the reactor can be illustrated with the following figure,
    where our new channel appears alongside standard reactor channels:

    ```
    Channel[TwoWay.Req[Int, String]]
        |
        |       #-----------------------#
        \       |                       |
         \------o--> links              |
                |                       |
                o--> main channel       |
                |                       |
                o--> sys channel        |
                |                       |
                #-----------------------#

    ```

    Note that the type of the 2-way server channel
    is `Channel[TwoWay.Req[Int, String]]`.
    If you would like to know what `TwoWay.Req[Int, String]]` type exactly is,
    you can study the implementation source code.
    However, if you only want to use the 2-way protocol,
    then understanding the implementation internals is not required,
    so we will skip that part.

    Next, let's start the client-side part of the protocol.
    The client must use the 2-way server channel to request a link.
    The `lengthServer` object that we saw earlier has a field `channel`
    that must be used for this purpose.
    Generally, this channel must be known to the client
    (only the `channel` must be shared, not the complete `lengthServer` object).
    To make things simple, we will instantiate the client-side part of the protocol
    in the same reactor as the server-side part.

    To connect to the server, the client must invoke the `connectTwoWay` extension
    method on the `channel`. This method is only available when the
    package `io.reactors.protocol` is imported, and works on 2-way server channels.
    The `connect` method returns an `IVar` (single element event stream),
    which is completed with a `TwoWay` object once the link is established.

    In the following, we connect to the server.
    Once the server responds,
    we use the `TwoWay[Int, String]` object to send a string event,
    and then print the length event that we get back:
    !*/

    /*!begin-code!*/
      lengthServer.channel.connect() onEvent { clientTwoWay =>
        clientTwoWay.output ! "What's my length?"
        clientTwoWay.input onEvent { len =>
          if (len == 17) println("received correct reply")
          else println("reply incorrect: " + len)
        }
      }
    }

    system.spawn(seeker)
    /*!end-code!*/

    /*!md
    After the link is established,
    the state of the reactor and its connectors is as shown in the following diagram:

    ```
                 #-----------------------#
                 |                       |
                 o--> links              |
                 |                       |
                 |                       |
          /---->[ ]-->                   |
          |     [ ]    serverTwoWay      |
          | /---[ ]<--                   |
          | |    |                       |
          | |    |                       |
          | \-->[ ]-->                   |
          |     [ ]    clientTwoWay      |
          \-----[ ]<--                   |
                 |                       |
                 o--> main channel       |
                 |                       |
                 o--> sys channel        |
                 |                       |
                 #-----------------------#
    ```

    Note that, in this case, the two-way channel has both endpoints in the same reactor.
    This is because we called `twoWayServe` and `connect` in the same reactor,
    for the purposes of demonstration.
    In real scenarios, we would typically invoke these two operations on separate
    reactors.
    !*/

    done.future.map(s => assert(s == "received correct reply"))
  }

  /*!md
  ### Two-Way Server Reactors

  In the next example, we instantiate the two-way protocol between two reactors.
  Furthermore, we use the short-hand version that both declares a reactor,
  and uses its *main channel* as the 2-way link server.
  We call this reactor a *2-way server*.

  To create a `Proto` object of a 2-way server,
  we use the `twoWayServer` extension method on `Reactor`.
  This method takes a lambda with
  the `server` state, which we saw earlier,
  whose `links` event stream emits established `twoWay` links.
  The lambda is invoked each time when a link is established.

  In the following, we create a reactor `seriesCalculator`,
  which emits elements of the series `1.0 / i`.
  For each `twoWay` link that is established,
  it responds to each integer `n` that it receives
  with a stream of events `1.0 / i`,
  where `i` ranges from `1` to `n`:
  !*/

  import io.reactors._
  import io.reactors.protocol._

  val system = ReactorSystem.default("test-system")

  test("two-way reactor server") {
    val done = Promise[Double]()
    def println(s: Double) = done.success(s)

    /*!begin-code!*/
    val seriesCalculator = Reactor.twoWayServer[Double, Int] {
      server =>
      server.links onEvent { twoWay =>
        twoWay.input onEvent { n =>
          for (i <- 1 until n) {
            twoWay.output ! (1.0 / i)
          }
        }
      }
    }
    val server = system.spawn(seriesCalculator)
    /*!end-code!*/

    /*!md
    ### Two-Way Connection Subscriptions

    We mentioned before that the 2-way server object has a `subscription` that can be
    used to stop the server and prevent establishing new links.
    However, existing links are not closed when the server is stopped.
    To close the existing links, each `TwoWay` object has its own `subscription`
    value.

    Let's write a client for the `seriesCalculator` reactor that we started previously.
    We request `2` series elements from the server,
    but unsubscribe immediately after receiving the first element:
    !*/

    /*!begin-code!*/
    system.spawnLocal[Unit] { self =>
      server.connect() onEvent { twoWay =>
        twoWay.output ! 2
        twoWay.input onEvent { x =>
          println(x)
          twoWay.subscription.unsubscribe()
        }
      }
    }
    /*!end-code!*/

    /*!md
    By running the client reactor,
    we can see that the second event from the server is never printed
    to the standard output.

    Note that the server-side `TwoWay` object is not closed in the previous example.
    In real scenarios,
    you should take care to additionally call `unsubscribe`
    on the server side `TwoWay` object.
    How the server decides that it is time to close the link is up to you - for
    example, the server could close the link when it receives a negative `n`.

    The `TwoWay` protocol is relatively low-level.
    It does not itself close its links,
    and delegates the task of doing so to its users.
    As such, its purpose is mainly to serve as a building block
    for higher-level protocols.
    !*/

    done.future.map(t => assert(t == 1.0))
  }
}
