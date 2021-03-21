/*!md
---
layout: tutorial
title: Reactors
topic: reactors
logoname: reactress-mini-logo-flat.png
projectname: Reactors.IO
homepage: http://reactors.io
permalink: /reactors/reactors/index.html
pagenum: 2
pagetot: 40
section: guide-main
---
!*/
package tutorial



/*!md
## Reactors 101
As we learned previously, event streams always propagate events on a single thread.
This is useful from the standpoint of program comprehension, but we still need a way
to express concurrency in our programs. In this section, we will see how this is done
with reactors.

A reactor is the basic unit of concurrency. For readers familiar with the actor model,
a reactor is close to the concept of an actor. While actors receive messages, reactors
receive events. However, while an actor in particular state has only a single point in
its definition where it can receive a message, a reactor can receive an event from
many different sources at any time. Despite this flexibility, one reactor will always
process **at most one** event at any time. We say that events received by a reactor
*serialize*, similar to how messages received by an actor are serialized.

As before, we start by importing the `io.reactors` package:
!*/
/*!begin-code!*/
import io.reactors._
/*!end-code!*/
/*!include-code Java:reactors-java-reactors-import.html!*/
import org.scalatest._
import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers



/*!md
To be able to create new reactors, we need a `ReactorSystem` object, which tracks
reactors in a single machine.
!*/
class Reactors extends AnyFunSuite with Matchers {

  /*!begin-code!*/
  val system = new ReactorSystem("test-system")
  /*!end-code!*/
  /*!include-code Java:reactors-java-reactors-system.html!*/

  test("simple reactor") {
    /*!md
    Before we can start a reactor instance, we need to define its template. One way to
    do this is to call `Reactor.apply[T]` method, which returns a `Proto` object for the
    reactor. The `Proto` object is called a *prototype* of the reactors.
    The following reactor prints all the events it receives to the standard output:
    !*/

    val received = Promise[String]()
    def println(x: String) = received.success(x)

    /*!begin-code!*/
    val proto: Proto[Reactor[String]] = Reactor[String] { self =>
      self.main.events onEvent {
        x => println(x)
      }
    }
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-anonymous.html!*/

    /*!md
    Let's examine this code more closely. The `Reactor.apply` method is called with the
    argument `String`. This means that the reactor encoded in the resulting `Proto`
    object only receives events whose type is `String`. This is the first difference
    with respect to the standard actor model, in which actors can receive messages of
    any type. Events received by reactors are well typed.

    In the reactor model, every reactor can access a special event stream called
    `main.events`, which emits events that the reactor receives from other reactors.
    Since we are declaring an anonymous reactor with the `Reactor.apply` method, we need
    to add a prefix `self.` to access members of the reactor.
    We previously learned that we can call `onEvent` to register callbacks to event
    streams, and we used it in this example to print the events using `println`.

    After defining a reactor template, the next step is to spawn a new reactor. We do
    this by calling the `spawn` method on the reactor system:
    !*/

    /*!begin-code!*/
    val ch: Channel[String] = system.spawn(proto)
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-spawn.html!*/

    /*!md
    The method `spawn` takes a `Proto` object as a parameter. The `Proto` object can
    generally encode the reactor's constructor arguments, scheduler, name and other
    options. In our example, we created a `Proto` object for an anonymous reactor
    with the `Reactor.apply` method, so we don't have any constructor arguments. We will
    later see alternative ways of declaring reactors and configuring prototypes.

    The method `spawn` does two things. First, it registers and starts a new reactor
    instance. Second, it returns a `Channel` object, which is used to send events to
    the newly created reactor. We can show the relationship between a reactor, its
    event stream and the channel as follows:

    ```
      "Hello world!"                            
        |              #-----------------------#
        |              |    Reactor[String]    |
        V              |                       |
    Channel[String] ---o--> Events[String]     |
          ^            |                       |
          |            |                       |
          |            #-----------------------#
       "Hola!"                                  
    ```

    The only way for the outside world to access the inside of a reactor is to send
    events to its channel. These events are eventually delivered to the corresponding
    event stream, which the reactor can listen to. The channel and event stream can only
    pass events whose type corresponds to the type of the reactor.

    Let's send an event to `HelloReactor`. We do this by calling the bang operator `!`
    on the channel:
    !*/

    /*!begin-code!*/
    ch ! "Hola!"
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-send.html!*/

    assert(Await.result(received.future, 5.seconds) == "Hola!")

    /*!md
    Running the last statement should print `"Hola!"` to the standard output.
    !*/
  }
}


/*!md
### Defining and configuring reactors

In the previous section, we saw how to define a reactor using the `Reactor.apply`
method. In this section, we take a look at an alternative way of defining a reactor --
by extending the `Reactor` class. Recall that the `Reactor.apply` method defines an
anonymous reactor template. Extending the `Reactor` class declares a named reactor
template.

In the following, we declare `HelloReactor`, which must be a top-level class:
!*/
/*!begin-code!*/
class HelloReactor extends Reactor[String] {
  main.events onEvent {
    x => println(x)
  }
}
/*!end-code!*/
/*!include-code Java:reactors-java-reactors-template.html!*/


class ReactorsTopLevel extends AnyFunSuite with Matchers {
  val system = new ReactorSystem("test-top-level")

  test("top-level reactor") {
    /*!md
    To run this reactor, we first create a prototype to configure it. The method
    `Proto.apply` takes the type of the reactor and returns a prototype for that
    reactor type. We then call the `spawn` method with that `Proto` object to start the
    reactor:
    !*/

    /*!begin-code!*/
    val ch = system.spawn(Proto[HelloReactor])
    ch ! "Howdee!"
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-spawn-template.html!*/

    /*!md
    We can also use the prototype to, for example, set the scheduler that the
    reactor instance should use. If we want the reactor instance to run on its
    dedicated thread to give it more priority, we can do the following:
    !*/

    /*!begin-code!*/
    system.spawn(Proto[HelloReactor].withScheduler(JvmScheduler.Key.newThread))
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-with-scheduler.html!*/

    /*!md
    Note that if you are running Reactors on Scala.js,
    you will need to use Scala.js-specific scheduler.
    The reason is that the JavaScript runtime is not multi-threaded.
    Asynchronous executions are placed on a single queue,
    and executed one after another.
    On Scala.js, you will therefore need to use the `JsScheduler.Key.default` scheduler.
    !*/

    /*!include-code Scala.js:reactors-scala-js-custom-scheduler.html!*/

    /*!md
    The call to `withScheduler` returns a new prototype that runs on a predefined
    scheduler called `ReactorSystem.Bundle.schedulers.newThread`. A reactor started like
    this is using this scheduler. Reactor systems allow registering custom schedulers.
    In the following, we define a custom `Timer` scheduler, which schedules the reactor
    for execution once every `1000` milliseconds:
    !*/

    /*!begin-code!*/
    system.bundle.registerScheduler("customTimer",
      new JvmScheduler.Timer(1000))
    val periodic = system.spawn(
      Proto[HelloReactor].withScheduler("customTimer"))
    periodic ! "Ohayo!"
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-custom-scheduler.html!*/

    Thread.sleep(2000)

    /*!md
    By running the code above, we can see that the event `"Ohayo!"` is processed only 1
    second after the reactor starts.

    There are several other configuration options for `Proto` objects, listed in the
    online API docs. We can summarize this section as follows -- starting a reactor is
    generally a three step process:

    1. A reactor template is created by extending the `Reactor` class.
    2. A reactor `Proto` configuration object is created with the `Proto.apply` method.
    3. A reactor instance is started with the `spawn` method of the reactor system.

    For convenience, we can fuse the first two steps by using the `Reactor.apply`
    method, which creates an anonymous reactor template and directly returns a
    prototype object of type `Proto[I]`, for some reactor type `I`.
    Typically, we do this in tests or in the REPL.
    !*/
  }
}


/*!md
## Using channels

Now that we understand how to create and configure reactors in different ways, we can
take a closer look at channels -- reactor's means of communicating with its environment.
As noted before, every reactor is created with a default channel called `main`, which is
usually sufficient. But sometimes a reactor needs to be able to receive more than just
one type of an event, and needs additional channels for this purpose.

Let's declare a reactor that stores key-value pairs. We can do this by defining the
following reactor:
!*/
/*!begin-code!*/
import scala.collection._

class PutOnlyReactor[K, V] extends Reactor[(K, V)] {
  val map = mutable.Map[K, V]()

  main.events onEvent {
    case (k, v) => map(k) = v
  }
}
/*!end-code!*/
/*!include-code Java:reactors-java-reactors-put-only.html!*/


/*!md
The `PutOnlyReactor` accepts events of type `(K, V)` for some generic type parameters
`K` and `V`. This is fine for the purposes of storing key-value pairs into this reactor,
but it does not make it possible to query values stored to specific keys. For this, the
sender must give the reactor the desired key of type `K` and a channel of type
`Channel[V]`, on which the value `V` can be sent back.

Since the same input channel serves two purposes, we need the following data type:
!*/
/*!begin-code!*/
trait Op[K, V]

case class Put[K, V](k: K, v: V) extends Op[K, V]

case class Get[K, V](k: K, ch: Channel[V]) extends Op[K, V]
/*!end-code!*/
/*!include-code Java:reactors-java-reactors-map-ops.html!*/


/*!md
With the `Op[K, V]` data type, we can define the following reactor:
!*/
/*!begin-code!*/
class MapReactor[K, V] extends Reactor[Op[K, V]] {
  val map = mutable.Map[K, V]()

  main.events onEvent {
    case Put(k, v) => map(k) = v
    case Get(k, ch) => ch ! map(k)
  }
}
/*!end-code!*/
/*!include-code Java:reactors-java-reactors-map-reactor.html!*/


class ReactorChannels extends AnyFunSuite with Matchers {
  val system = new ReactorSystem("test-channels")

  test("channel creation") {
    val received = Promise[List[String]]()
    def println(x: List[String]) = received.success(x)

    /*!md
    Let's start `MapReactor` and test it. We will use the `MapReactor` to store some
    DNS aliases. We will map each alias `String` key to a URL, where the URLs are
    represented with the `List[String]` type. We first initialize as follows:
    !*/

    /*!begin-code!*/
    val mapper = system.spawn(Proto[MapReactor[String, List[String]]])
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-spawn-mapper.html!*/

    /*!md
    We then send a couple of `Put` messages to store some alias values:
    !*/

    /*!begin-code!*/
    mapper ! Put("dns-main", "dns1" :: "lan" :: Nil)
    mapper ! Put("dns-backup", "dns2" :: "com" :: Nil)
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-send-mapper.html!*/

    Thread.sleep(1000)

    /*!md
    Next, we create a client reactor that we control by sending it `String` events. This
    means that the reactor's type will be `Reactor[String]`. However, the client reactor
    will also have to contact the `MapReactor` and ask it for one of the URLs. Since the
    `MapReactor` can only send it back events that are `List[String]`, the client's
    default channel might not generally be able to receive the reply. The client will
    have to provide the `MapReactor` with a different channel. The following expression
    is used to create a new channel:

    ```
    val c: Connector[EventType] = system.channels.open[EventType]
    ```

    The `Connector` object contains two members: `channel`, which is the newly created
    channel, and `events`, which is the event stream corresponding to that channel. The
    event stream propagates all events that were sent and delivered on the channel, and
    can only be used by the reactor that created it. The channel, on the other hand,
    *can* be shared with other reactors.

    > Event streams are not shareable objects -- never send an event stream created by
    > one reactor to some other reactor.

    The expression `system.channels` returns a channel builder object, which provides
    methods like `named` or `daemon`, used to customize the channel (see online API docs
    for more details). In this example, we will use the `daemon` channel, to indicate
    that the channel does not need to be closed (more on that a bit later). To create a
    new channel, we call `open` on the channel builder with the appropriate type
    parameter.

    Let's define a client reactor that waits for a `"start"` message, and then checks
    a DNS entry. This reactor will use the `onMatch` handler instead of `onEvent`, to
    listen only to certain `String` events and ignore others:
    !*/

    /*!begin-code!*/
    val ch = system.spawn(Reactor[String] { self =>
      self.main.events onMatch {
        case "start" =>
          val reply = self.system.channels.daemon.open[List[String]]
          mapper ! Get("dns-main", reply.channel)
          reply.events onEvent { url =>
            println(url)
          }
        case "end" =>
          self.main.seal()
      }
    })
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-mapper-client.html!*/

    /*!md
    Above, when the reactor receives the `"start"` event, it opens a new channel `reply`
    that accepts `List[String]` events. It then sends the `MapReactor` a `Get` event
    with the `"dns-main"` key and the channel. Finally, the reactor listens to events
    sent back and prints the URL to the standard output.

    Another new thing in this code is in the `"end"` case of the pattern match. Here,
    the reactor calls `seal` on the main channel to indicate that it will not receive
    any further events on that channel. Once all non-daemon channels become sealed, the
    reactor terminates.

    > A reactor terminates either when all its non-daemon channels are sealed, or when
    > its constructor or some event handler throws an exception.

    Let's start the client reactor and see what happens:
    !*/

    /*!begin-code!*/
    ch ! "start"
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-mapper-client-start.html!*/

    assert(Await.result(received.future, 5.seconds) == "dns1" :: "lan" :: Nil)

    /*!md
    At this point, we should witness the URL on the standard output.
    Finally, we can send the `"end"` message to the client reactor to stop it.
    !*/

    /*!begin-code!*/
    ch ! "end"
    /*!end-code!*/
    /*!include-code Java:reactors-java-reactors-mapper-client-end.html!*/
  }
}
