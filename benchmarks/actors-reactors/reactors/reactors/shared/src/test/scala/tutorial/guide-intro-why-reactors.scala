/*!md
---
layout: tutorial
title: What are Reactors?
topic: reactors
logoname: reactress-mini-logo-flat.png
projectname: Reactors.IO
homepage: http://reactors.io
permalink: /reactors/why-reactors/index.html
pagenum: 1
pagetot: 40
section: guide-intro
---
!*/
package tutorial



import org.scalatest._
import scala.concurrent.ExecutionContext
import org.scalatest.funsuite.AsyncFunSuite



/*!md
## What are Reactors?

**Reactors** is a foundational framework for concurrent and distributed systems.
It allows you to create concurrent and distributed applications more easily,
by providing correct, robust and composable programming abstractions.

Based on the **reactor model** for distributed programming,
Reactors allow writing location-transparent programs,
that can be easily subdivided into modular components.
At the same time, clear separation between units of concurrency called *reactors*
makes it easier to reason about concurrent programs.

At the core of this reactor programming model,
the improved composition is the result of
a careful integration of the traditional actor model
and functional reactive programming concepts.


### Event-driven

Reactors comprise an event-driven programming model.
Clients can subscribe and react to event streams,
which asynchronously produce events.
This makes the reactor model well-suited for interactive applications such as UIs,
but also ideal for building distributed software,
which is typically characterized by latency and asynchrony.


### Functional

While the concept of event streams and callbacks
resembles the principles found in traditional actor systems,
event streams are first-class, functional values.
They can be declaratively composed and manipulated
in a similar fashion as Scala collections or Java streams.
Reactive, incremental data structures can
also be transformed with high-level functional operators.

Despite the fact that a declarative approach is usually more concise,
users can gradually transition to a more functional style.
In fact, you can decide to blend the two styles
to the degree that you see fit.


### Concurrent and distributed

The reactor model organizes computations
into basic units of concurrency called reactors.
Inside each reactor, computation is sequential,
which simplifies program comprehension and accessing reactor state.
Separate reactors communicate by exchanging events through channels.

At the same time,
the reactor model is location-transparent.
This means that you can develop and test the program on a single machine,
and then seamlessly deploy it on multiple machine that are connected
with a computer network.


### Modular

The subtle interplay between channels and event streams
allows composing powerful message exchange protocols in a modular fashion.
In addition to a rich library of composable message protocols,
clients can implement and modularize their own message exchange patterns,
and later use them in concrete reactors.


### Multiple frontends

At the time of writing this document,
the Reactors framework has bindings for both Scala and Scala.JS,
as well as Java.
Additional frontends are planned in the future.

You can download Reactors from
[http://reactors.io/download/](http://reactors.io/download/).


## Why Reactors?

Writing concurrent and distributed programs is hard.
Ensuring correctness, scalability and fault-tolerance is even harder.
There are many reasons why this is the case,
and below we list some of them:

- First of all, most concurrent and distributed computations are by nature
  non-deterministic. This non-determinism is not a consequence of poor programming
  abstractions, but is inherent in systems that need to react to external events.
- Data races are a characteristic of shared-memory multicore systems.
  Combined with inherent non-determinism, these lead to subtle bugs that are hard to
  detect or reproduce.
- Random faults, network outages, or interruptions present in distributed programming
  compromise correctness and robustness of distributed systems.
- Shared-memory programs do not work in distributed environments,
  and existing shared-memory programs are not easily ported to a distributed setup.
- It is extremely hard to correctly compose concurrent and distributed programs.
  Correctness of specific components is no guarantee for global program correctness
  when those components are used together.

The consequence of all this is that concurrent and distributed programming are
costly and hard to get right.
It is even an established practice in many companies
to avoid multi-threaded code whenever possible.

There are frameworks out there that try to address the aforementioned problems
with concurrent and distributed programming.
While in some cases these issues are partially addressed by some existing frameworks,
Reactors go a step further.
In particular, the Reactors framework is based on the following:

- Location-transparent **reactors**, lightweight entities that execute concurrently with
  each other, but are internally always single-threaded,
  and can be ported from a single machine to a distributed setting.
- Asynchronous first-class **event streams** that can be reasoned about
  in a declarative, functional manner, and are the basis for composing components.
- **Channels** that can be shared between reactors, and are used to asynchronously
  send events.

These three unique abstractions are the core prerequisite
for building powerful distributed computing abstractions.
Most other utilities in the Reactors framework are built in terms of reactors,
channels and event streams.
!*/
class GuideWhyReactors extends AsyncFunSuite {
  implicit override def executionContext = ExecutionContext.Implicits.global
}
