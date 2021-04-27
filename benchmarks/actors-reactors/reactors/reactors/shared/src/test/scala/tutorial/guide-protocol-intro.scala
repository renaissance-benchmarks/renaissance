/*!md
---
layout: tutorial
title: Introduction to Protocols
topic: reactors
logoname: reactress-mini-logo-flat.png
projectname: Reactors.IO
homepage: http://reactors.io
permalink: /reactors/protocol-intro/index.html
pagenum: 1
pagetot: 40
section: guide-protocol
---
!*/
package tutorial



import org.scalatest._
import scala.collection._
import scala.concurrent.ExecutionContext
import scala.concurrent.Promise
import org.scalatest.funsuite.AsyncFunSuite



/*!md
## Protocols in the Reactor Model

The basic primitives of the reactor model - reactors, event streams and channels - allow
composing powerful communication abstractions.
In the following sections, we will go through some of the basic communication protocols
that the Reactors framework supports.
What these protocols have in common is
that they are not artificial extensions of the basic model.
Rather, they are composed from basic abstractions and simpler protocols.

In this section, we go through one of the simplest protocols,
namely the **server-client** protocol.
We first show how to implement a simple server-client protocol ourselves.
After that, we show how to use the standard server-client implementation
provided by the Reactors framework.
Note that, in the later sections on protocols,
we will not dive into the implementation,
but instead immediately show how to use the already implemented protocol
provided by the framework.

This will serve several purposes.
First, you should get an idea of how to implement a communication pattern
using event streams and channels.
Second, you will see that there is more than one way
to implement a protocol and expose it to clients.
Finally, you will see how protocols are structured in the Reactors framework.
!*/
class GuideServerProtocol extends AsyncFunSuite {

  implicit override def executionContext = ExecutionContext.Implicits.global

  test("custom server-client implementation") {
    val done = Promise[String]()
    def println(x: String) = done.success(x)

    /*!md
    ### Custom Server-Client Protocol

    Let's implement the server-client protocol ourselves.
    Before we start, we import the contents of the `io.reactors` package.
    We then create a default reactor system:
    !*/

    /*!begin-code!*/
    import io.reactors._

    val system = ReactorSystem.default("test-system")
    /*!end-code!*/

    /*!md
    Let's now consider the server-client protocol more closely.
    This protocol proceeds as follows: first, the client sends a request value to the
    server. Then, the server uses the request to compute a response value and send
    it to the client. But to do that, the server needs a response channel to send the
    value along. This means that the client must not only send the request value to
    the server, but also send it a channel used for the reply.
    The request sent by the client is thus a tuple with a value and the reply channel.
    The channel used by the server must accept such tuples.
    We capture these relations with the following two types:
    !*/

    /*!begin-code!*/
    type Req[T, S] = (T, Channel[S])

    type Server[T, S] = Channel[Req[T, S]]
    /*!end-code!*/

    /*!md
    Here, the `T` is type of the request value,
    and `S` is the type of the response value.
    The `Req` type represents the request - a tuple of the request value `T` and
    the reply channel for responses `S`.
    The `Server` type is then just a channel that accepts request objects.

    Question arises - how can we create a `Server` channel?
    There are several requirements that a factory method for the `Server` channel
    should satisfy.
    First, it should be generic in the request and the response type.
    Second, it should be generic in how the request type is mapped to the response type.
    Third, when a request is sent to the server, the mapped response should be sent
    back to the server.
    Putting these requirements together, we arrive at the following implementation
    of the `server` method, which instantiates a new server:
    !*/

    /*!begin-code!*/
    def server[T, S](f: T => S): Server[T, S] = {
      val c = system.channels.open[Req[T, S]]
      c.events onMatch {
        case (x, reply) => reply ! f(x)
      }
      c.channel
    }
    /*!end-code!*/

    /*!md
    The `server` method starts by creating a connector for `Req[T, S]` type.
    It then adds a callback to the event stream of the newly created connector.
    The callback decomposes the request into the request value `x` of type `T` and
    the `reply` channel, then maps the input value using the specified mapping
    function `f`, and finally sends the mapped value of type `S` back along the `reply`
    channel. The `server` method returns the channel associated with this connector.

    We can use this method to start a server that maps input strings into
    uppercase strings, as follows:
    !*/

    /*!begin-code!*/
    val proto = Reactor[Unit] { self =>
      val s = server[String, String](_.toUpperCase)
    }
    system.spawn(proto)
    /*!end-code!*/

    /*!md
    Next, we will implement the client protocol.
    We will define a new method `?` on the `Channel` type,
    which sends the request to the server.
    This method cannot immediately return the server's response, because the response
    arrives asynchronously. Instead, `?` must return an event stream with the
    server's reply.
    So, the `?` method must create a reply channel,
    send the `Req` object to the server, and then return the event stream associated
    with the reply channel.
    This is shown in the following:
    !*/

    /*!begin-code!*/
    implicit class ChannelOps[T, S: Arrayable](val s: Server[T, S]) {
      def ?(x: T): Events[S] = {
        val reply = system.channels.daemon.open[S]
        s ! (x, reply.channel)
        reply.events
      }
    }
    /*!end-code!*/

    /*!md
    We show the interaction between the server and the client by instantiating the
    two protocols within the same reactor.
    The server just returns an uppercase version of the input string,
    while the client sends the request with the content `"hello"`,
    and prints the response to the standard output.
    This is shown in the following snippet:
    !*/

    /*!begin-code!*/
    val serverClient = Reactor[Unit] { self =>
      val s = server[String, String](_.toUpperCase)

      (s ? "hello") onEvent { upper =>
        println(upper)
      }
    }
    system.spawn(serverClient)
    /*!end-code!*/

    /*!md
    Our implementation works, but it is not very useful to start the server-client
    protocol inside a single reactor. Normally, the server and the client are
    separated by the network, or are at least different reactors running inside the
    same reactor system.

    It turns out that, with our current toy implementation, it is not straightforward
    to instantiate the server-client protocol in two different reactors.
    The main reason for this is that once the server channel is instantiated
    within one reactor, we have no way of *seeing* it in another reactor.
    We will see how to easily overcome this problem
    when using the standard server-client implementation in the Reactors framework.
    !*/

    done.future.map(t => assert(t == "HELLO"))
  }

  /*!md
  ### Standard Server-Client Protocol

  We have just seen an example implementation of the server-client protocol,
  which relies solely on the basic primitives provided by the Reactors framework.
  However, the implementation that was presented is very simplistic,
  and it ignores several important concerns.
  For example, how do we stop the server protocol?
  Then, in our toy example,
  we instantiated the server-client protocol in a single reactor,
  but is it possible to instantiate server-client in two different reactors?

  In this section, we take a close look at how the server-client protocol is exposed
  in the Reactors framework, and explain how some of the above concerns are addressed.
  Most predefined protocols can be instantiated in several ways:

  - By installing the protocol on the existing connector inside an existing reactor,
    which has an appropriate type for that protocol. This has the benefit that you
    can install the protocol on, for example, the main channel of a reactor. It also
    makes the protocol accessible to other reactors that are aware of that respective
    channel.
  - By creating a new connector for the protocol, and then installing the protocol
    to that connector. This has the benefit that you can fully customize the protocol's
    connector (for example, name it), but you will need to find some way of sharing
    the protocol's channel with other reactors - for example, by relying on the
    `Channels` service, or by sending the channel to specific reactors.
  - By creating a new `Proto` object for a reactor that exclusively runs a specific
    protocol. This has the benefit of being able to fully configure both the reactor
    that you wish to start (e.g. specify a scheduler, reactor name or transport).
  - By immediately spawning a reactor that runs a specific protocol. This is the most
    concise option.

  These approaches are mostly equivalent, but they offer different
  tradeoffs between convenience and customization.
  Let's take a look at the predefined server-client protocol to study these approaches
  in turn.
  !*/

  test("standard server-client protocol - existing connector") {
    val done = Promise[Int]()
    def println(x: Int) = done.success(x)

    /*!md
    #### Adding a Protocol with an Existing Connector

    We first import the `io.reactors` and `io.reactors.protocol` packages,
    and then instantiate the default reactor system:
    !*/

    /*!begin-code!*/
    import io.reactors._
    import io.reactors.protocol._

    val system = ReactorSystem.default("test-system")
    /*!end-code!*/

    /*!md
    When using an existing connector, we need to ensure that the connector's type
    matches the type needed by the protocol. In the case of a server, the connector's
    event type must be `Server.Req`. In the following, we define a server prototype
    that multiplies the request integer by `2`. To install the server-client protocol,
    we call the `serve` method on the connector:
    !*/

    /*!begin-code!*/
    val proto = Reactor[Server.Req[Int, Int]] { self =>
      self.main.serve(x => x * 2)
    }
    val server = system.spawn(proto)
    /*!end-code!*/

    /*!md
    The client can then query the server in the standard way, using the `?` operator:
    !*/

    /*!begin-code!*/
    system.spawnLocal[Unit] { self =>
      (server ? 7) onEvent { response =>
        println(response)
      }
    }
    /*!end-code!*/

    done.future.map(t => assert(t == 14))
  }

  test("standard server-client protocol - new connector") {
    import io.reactors._
    import io.reactors.protocol._

    val system = ReactorSystem.default("test-system")
    val done = Promise[Int]()
    def println(x: Int) = done.success(x)

    /*!md
    #### Adding a Protocol to a New Connector

    Let's say that the main channel is already used for something else - for example,
    the main channel could be accepting termination requests. Here, the main
    channel cannot be shared with the server protocol - protocols usually need exclusive
    ownership of the respective channel.
    In this case, we want to create a new connector for the protocol.

    This approach is very similar to using an existing connector.
    The only difference is that we must first create the connector itself,
    which gives us an opportunity to customize it.
    In particular, we will make the server a `daemon` channel,
    and we will assign it a specific name `"server"`,
    so that other reactors can find it.
    We will name the reactor itself `"Multiplier"`.
    To create a server connector, we use the convenience method called `server`
    on the channel builder object:
    !*/

    /*!begin-code!*/
    val proto = Reactor[String] { self =>
      self.main.events onMatch {
        case "terminate" => self.main.seal()
      }

      self.system.channels.daemon.named("server").server[Int, Int].serve(_ * 2)
    }
    system.spawn(proto.withName("Multiplier"))
    /*!end-code!*/

    /*!md
    The client must now query the name service to find the server channel,
    and from there on it proceeds as before:
    !*/

    /*!begin-code!*/
    system.spawnLocal[Unit] { self =>
      self.system.channels.await[Server.Req[Int, Int]](
        "Multiplier", "server"
      ) onEvent { server =>
        (server ? 7) onEvent { response =>
          println(response)
        }
      }
    }
    /*!end-code!*/

    done.future.map(t => assert(t == 14))
  }

  test("standard server-client protocol - prototype") {
    import io.reactors._
    import io.reactors.protocol._

    val system = ReactorSystem.default("test-system")
    val done = Promise[Int]()
    def println(x: Int) = done.success(x)

    /*!md
    #### Creating a Reactor Prototype for a Specific Protocol

    When we are sure that the reactor will exist only, or mainly,
    for the purposes of the server protocol,
    we can directly create a reactor server.
    To do this, we use the `server` method on the `Reactor` companion object.
    The `server` method returns the `Proto` object for the server,
    which can then be further customized before spawning the reactor.
    The `server` method takes a user function that is invoked each time a request
    arrives. This user function takes the state of the server and the request event,
    and returns the response event.

    Here is an example:
    !*/

    /*!begin-code!*/
    val proto = Reactor.server[Int, Int]((state, x) => x * 2)
    val server = system.spawn(proto)

    system.spawnLocal[Unit] { self =>
      (server ? 7) onEvent { response =>
        println(response)
      }
    }
    /*!end-code!*/

    /*!md
    The state object for the server contains the `Subscription` object,
    which allows the users to stop the server if an unexpected event arrives.
    !*/

    done.future.map(t => assert(t == 14))
  }

  test("standard server-client protocol - spawn") {
    import io.reactors._
    import io.reactors.protocol._

    val system = ReactorSystem.default("test-system")
    val done = Promise[Int]()
    def println(x: Int) = done.success(x)

    /*!md
    #### Spawning a Reactor for a Specific Protocol

    Finally, we can immediately start a server reactor, without any customization.
    This is done by passing a server function to the `server` method on the
    `ReactorSystem`, as follows:
    !*/

    /*!begin-code!*/
    val server = system.server[Int, Int]((state, x) => x * 2)

    system.spawnLocal[Unit] { self =>
      (server ? 7) onEvent { response =>
        println(response)
      }
    }
    /*!end-code!*/

    /*!md
    In the following sections, we will take a look at some other predefined protocols.
    Generally, these protocols will have a similar usage structure.
    !*/

    done.future.map(t => assert(t == 14))
  }
}
