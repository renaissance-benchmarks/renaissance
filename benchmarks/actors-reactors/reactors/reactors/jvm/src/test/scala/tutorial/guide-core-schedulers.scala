/*!md
---
layout: tutorial
title: Schedulers and Reactor Lifecycle
topic: reactors
logoname: reactress-mini-logo-flat.png
projectname: Reactors.IO
homepage: http://reactors.io
permalink: /reactors/schedulers-and-lifecycle/index.html
pagenum: 3
pagetot: 40
section: guide-main
---
!*/
package tutorial



/*!md
## Schedulers

Each reactor template can be used to start multiple reactor instances,
and each reactor instance can be started with a different reactor scheduler.
Different schedulers have different characteristics in terms of execution priority,
frequency, latency and throughput.
In this section, we'll take a look at how to use a non-default scheduler,
and how to define custom schedulers when necessary.

We start with the import of the standard Reactors.IO package:
!*/
/*!begin-code!*/
import io.reactors._
/*!end-code!*/
/*!include-code Java:reactors-java-schedulers-import.html!*/
import org.scalatest._
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers


object SchedulersMockup {
  val fakeSystem = new FakeSystem
  def println(x: String) = fakeSystem.out.println(x)
}
import SchedulersMockup._


/*!md
We then define a reactor that logs incoming events,
reports every time it gets scheduled,
and ends after being scheduled three times.
We will use the `sysEvents` stream of the reactor,
which will be explained shortly -
for now, all you need to know is that this stream produces
events when the reactor gets some execution time (i.e. gets scheduled),
and pauses its execution (i.e. gets preempted).
!*/
/*!begin-code!*/
class Logger extends Reactor[String] {
  var count = 3
  sysEvents onMatch {
    case ReactorScheduled =>
      println("scheduled")
    case ReactorPreempted =>
      count -= 1
      if (count == 0) {
        main.seal()
        println("terminating")
      }
  }
  main.events.onEvent(println)
}
/*!end-code!*/
/*!include-code Java:reactors-java-schedulers-logger.html!*/


class Schedulers extends AnyFunSuite with Matchers {
  /*!md
  Before starting, we need to create a reactor system,
  as we learned in the previous sections:
  !*/

  /*!begin-code!*/
  val system = new ReactorSystem("test-system")
  /*!end-code!*/
  /*!include-code Java:reactors-java-schedulers-system.html!*/

  test("custom global execution context scheduler") {
    /*!md
    Every reactor system is bundled with a default scheduler
    and some additional predefined schedulers.
    When a reactor is started, it uses the default scheduler,
    unless specified otherwise.
    In the following, we override the default scheduler with the one using Scala's
    global execution context, i.e. Scala's own default thread pool:
    !*/

    /*!begin-code!*/
    val proto = Proto[Logger].withScheduler(
      JvmScheduler.Key.globalExecutionContext)
    val ch = system.spawn(proto)
    /*!end-code!*/
    /*!include-code Java:reactors-java-schedulers-global-ec.html!*/

    assert(fakeSystem.out.queue.take() == "scheduled")

    /*!md
    In Scala.js, there is no multi-threading - executions inside a single JavaScript
    runtime must execute in a single thread. For this reason, you will need to use
    a special `JsScheduler.Key.default` instance with the Scala.js frontend.
    !*/

    /*!include-code Scala.js:reactors-scala-js-custom-scheduler.html!*/

    /*!md
    Running the snippet above should start the `Logger` reactor and print `scheduled`
    once, because starting a reactor schedules it even before any events arrive.
    If we now send an event to the main channel, we will see `scheduled` printed again,
    followed by the event itself.
    !*/

    Thread.sleep(1000)

    /*!begin-code!*/
    ch ! "event 1"
    /*!end-code!*/
    /*!include-code Java:reactors-java-schedulers-global-ec-send.html!*/

    assert(fakeSystem.out.queue.take() == "scheduled")
    assert(fakeSystem.out.queue.take() == "event 1")

    /*!md
    Sending the event again decrements the reactor's counter.
    The main channel gets sealed, leaving the reactor in a state without non-daemon
    channels, and the reactor terminates:
    !*/

    Thread.sleep(1000)

    /*!begin-code!*/
    ch ! "event 2"
    /*!end-code!*/
    /*!include-code Java:reactors-java-schedulers-global-ec-send-again.html!*/

    assert(fakeSystem.out.queue.take() == "scheduled")
    assert(fakeSystem.out.queue.take() == "event 2")
    assert(fakeSystem.out.queue.take() == "terminating")
  }
}


/*!md

## Reactor Lifecycle

Every reactor goes through a certain set of stages during its lifetime,
jointly called a **reactor lifecycle**.
When the reactor enters a specific stage, it emits a lifecycle event.
All lifecycle events are dispatched on a special daemon event stream called `sysEvents`.
Every reactor is created with this event stream.

The reactor lifecycle is as follows:

- After calling `spawn`,
  the reactor is scheduled for execution.
  Its constructor is started asynchronously,
  and immediately after that,
  a `ReactorStarted` event is dispatched.
- Then, whenever the reactor gets execution time,
  the `ReactorScheduled` event is dispatched.
  After that, some number of events are dispatched on normal event streams.
-  When the scheduling system decides to preempt the reactor,
  the `ReactorPreempted` event is dispatched.
  This scheduling cycle can be repeated any number of times.
- Eventually, the reactor terminates,
  either by normal execution or exceptionally.
  If a user code exception terminates execution,
  a `ReactorDied` event is dispatched.
- In either normal or exceptional execution,
  `ReactorTerminated` event gets emitted.

This reactor lifecycle is shown in the following diagram:

```
    |
    V
ReactorStarted
    |
    V
ReactorScheduled <----
    |                 \
    V                 /
ReactorPreempted -----
    |                 \
    |            ReactorDied
    V                 /
ReactorTerminated <---
    |
    x
```

To test this, we define the following reactor:
!*/
/*!begin-code!*/
class LifecycleReactor extends Reactor[String] {
  var first = true
  sysEvents onMatch {
    case ReactorStarted =>
      println("started")
    case ReactorScheduled =>
      println("scheduled")
    case ReactorPreempted =>
      println("preempted")
      if (first) first = false
      else throw new Exception("Manually thrown.")
    case ReactorDied(_) =>
      println("died")
    case ReactorTerminated =>
      println("terminated")
  }
}
/*!end-code!*/
/*!include-code Java:reactors-java-schedulers-lifecycle.html!*/


class Lifecycle extends AnyFunSuite with Matchers {
  val system = new ReactorSystem("test-system")

  test("lifecycle throws an exception") {
    /*!md
    Upon creating the lifecycle reactor,
    the reactor gets the `ReactorStarted` event,
    and then `ReactorStarted` and `ReactorScheduled` events.
    The reactor then gets suspended,
    and remains that way until the scheduler gives it more execution time.
    !*/

    /*!begin-code!*/
    val ch = system.spawn(Proto[LifecycleReactor])
    /*!end-code!*/
    /*!include-code Java:reactors-java-schedulers-lifecycle-spawn.html!*/

    assert(fakeSystem.out.queue.take() == "started")
    assert(fakeSystem.out.queue.take() == "scheduled")
    assert(fakeSystem.out.queue.take() == "preempted")

    Thread.sleep(1000)

    /*!md
    The scheduler executes the reactor again
    when it detects that there are pending messages.
    If we send an event to the reactor now,
    we can see the same cycle of `ReactorScheduled` and `ReactorPreempted`
    on the standard output.
    However, the `ReactorPreempted` handler this time throws an exception.
    The exception is caught, `ReactorDied` event is emitted,
    followed by the mandatory `ReactorTerminated` event.
    !*/

    /*!begin-code!*/
    ch ! "event"
    /*!end-code!*/
    /*!include-code Java:reactors-java-schedulers-lifecycle-send.html!*/

    /*!md
    At this point, the reactor is fully removed from the reactor system.
    !*/

    assert(fakeSystem.out.queue.take() == "scheduled")
    assert(fakeSystem.out.queue.take() == "preempted")
    assert(fakeSystem.out.queue.take() == "died")
    assert(fakeSystem.out.queue.take() == "terminated")
  }
}
