package io.reactors



import io.reactors.common._
import scala.collection._
import scala.runtime.IntRef
import scala.util.Random
import scala.util.Failure
import scala.util.Success
import scala.util.Try



/** A basic event stream.
 *
 *  Event streams are special objects that may produce events of a certain type `T`.
 *  Clients may subscribe side-effecting functions (i.e. callbacks)
 *  to these events with `onReaction`, `onEvent`, `onMatch` and `on` --
 *  each of these methods will invoke the callback when an event
 *  is produced, but some may be more suitable depending on the use-case.
 *
 *  An event stream produces events until it ''unreacts''.
 *  After the event stream unreacts, it never produces an event again.
 *
 *  Event streams can also be manipulated using declarative combinators
 *  such as `map`, `filter`, `until`, `after` and `scanPast`:
 *
 *  {{{
 *  def positiveSquares(r: Events[Int]) = r.map(x => x * x).filter(_ != 0)
 *  }}}
 *
 *  With the exception of `onX` family of methods, and unless otherwise specified,
 *  operators passed to these declarative combinators should be pure -- they should not
 *  have any side-effects.
 *
 *  The result of applying a declarative combinator on `Events[T]` is usually
 *  another `Events[S]`, possibly with a type parameter `S` different from `T`.
 *  Event sink combinators, such as `onEvent`, return a `Subscription` object used to
 *  `unsubscribe` from their event source.
 *
 *  Combinators that start with the prefix `on`, `to`, `pipe` or `get` are called *sink
 *  combinators*. Calling these combinators subscribes to the event stream and creates
 *  a subscription object. The event source is from there on responsible for propagating
 *  events to sink combinators until it either *unreacts*, meaning that it will not
 *  emit any other events, or the event sink gets *unsubscribed*. The event sink can be
 *  unsubscribed by calling the `unsubscribe` method of the `Subscription` object.
 *  The client is responsible for unsubscribing from an event source once the events are
 *  no longer needed. Failure to do so risks *time leaks*, a form of resource leak in
 *  which the program gets slower and slower (because it needs to propagate no longer
 *  needed events).
 *
 *  Event streams are specialized for `Int`, `Long` and `Double`.
 *
 *  Every event stream is bound to a specific `Reactor`, the basic unit of concurrency.
 *  Within a reactor, at most a single event stream propagates events at a time.
 *  An event stream will only produce events during the execution of that reactor --
 *  events are never triggered on a different reactor.
 *  It is forbidden to share event streams between reactors.
 *
 *  @author        Aleksandar Prokopec
 *
 *  @tparam T      type of the events in this event stream
 */
trait Events[@spec(Int, Long, Double) T] {
  /** Registers a new `observer` to this event stream.
   *
   *  The `observer` argument may be invoked multiple times -- whenever an event is
   *  produced, or an exception occurs, and at most once when the event stream is
   *  terminated. After the event stream terminates, no events or exceptions are
   *  propagated on this event stream any more.
   *
   *  @param observer    the observer for `react`, `except` and `unreact` events
   *  @return            a subscription for unsubscribing from reactions
   */
  def onReaction(observer: Observer[T]): Subscription

  /** Registers callbacks for react and unreact events.
   *
   *  A shorthand for `onReaction` -- the specified functions are invoked whenever there
   *  is an event or an unreaction.
   *
   *  @param reactFunc   called when this event stream produces an event
   *  @param unreactFunc called when this event stream unreacts
   *  @return            a subscription for unsubscribing from reactions
   */
  def onEventOrDone(reactFunc: T => Unit)(unreactFunc: =>Unit): Subscription = {
    val observer = new Events.OnEventOrDone(reactFunc, () => unreactFunc)
    onReaction(observer)
  }

  /** Registers callback for react events.
   *
   *  A shorthand for `onReaction` -- the specified function is invoked whenever
   *  there is an event.
   *
   *  @param observer    the callback for events
   *  @return            a subcriptions for unsubscribing from reactions
   */
  def onEvent(observer: T => Unit): Subscription = {
    onEventOrDone(observer)(() => {})
  }

  /** Registers callback for events that match the specified patterns.
   *
   *  A shorthand for `onReaction` -- the specified partial function is applied
   *  to only those events for which it is defined.
   *
   *  This method only works for `AnyRef` values.
   *
   *  Example:
   *
   *  {{{
   *  r onMatch {
   *    case s: String => println(s)
   *    case n: Int    => println("number " + s)
   *  }
   *  }}}
   *
   *  '''Use case''':
   *
   *  {{{
   *  def onMatch(reactor: PartialFunction[T, Unit]): Subscription
   *  }}}
   *
   *  @param observer    the callback for those events for which it is defined
   *  @return            a subscription for unsubscribing from reactions
   */
  def onMatch(observer: PartialFunction[T, Unit])(implicit sub: T <:< AnyRef):
    Subscription = {
    onReaction(new Observer[T] {
      def react(event: T, hint: Any) = {
        if (observer.isDefinedAt(event)) observer(event)
      }
      def except(t: Throwable) {
        throw UnhandledException(t)
      }
      def unreact() {}
    })
  }

  /** Registers a callback for react events, disregarding their values
   *
   *  A shorthand for `onReaction` -- called whenever an event occurs.
   *
   *  This method is handy when the precise event value is not important,
   *  or the type of the event is `Unit`.
   *
   *  @param observer    the callback invoked when an event arrives
   *  @return            a subscription for unsubscribing from reactions
   */
  def on(observer: =>Unit)(implicit dummy: Spec[T]): Subscription = {
    onReaction(new Events.On[T](() => observer))
  }

  /** Executes the specified block when `this` event stream unreacts.
   *
   *  @param observer    the callback invoked when `this` unreacts
   *  @return            a subscription for the unreaction notification
   */
  def onDone(observer: =>Unit)(implicit dummy: Spec[T]): Subscription = {
    onReaction(new Events.OnDone[T](() => observer))
  }

  /** Executes the specified block when `this` event stream forwards an exception.
   *
   *  @param pf          the partial function used to handle the exception
   *  @return            a subscription for the exception notifications
   */
  def onExcept(pf: PartialFunction[Throwable, Unit]): Subscription = {
    onReaction(new Observer[T] {
      def react(value: T, hint: Any) {}
      def except(t: Throwable) {
        if (pf.isDefinedAt(t)) pf(t)
        else throw UnhandledException(t)
      }
      def unreact() {}
    })
  }

  /** Transforms emitted exceptions into an event stream.
   *
   *  If the specified partial function is defined for the exception,
   *  an event is emitted.
   *  Otherwise, the same exception is forwarded.
   *
   *  @tparam U          type of events exceptions are mapped to
   *  @param  pf         partial mapping from functions to events
   *  @return            an event stream that emits events when an exception arrives
   */
  def recover[U >: T](pf: PartialFunction[Throwable, U])(implicit evid: U <:< AnyRef):
    Events[U] =
    new Events.Recover(this, pf, evid)

  /** Returns an event stream that ignores all exceptions in this event stream.
   *
   *  @return            an event stream that forwards all events,
   *                     and ignores all exceptions
   */
  def ignoreExceptions: Events[T] = new Events.IgnoreExceptions(this)

  /** Converts this event stream into an event stream of reactions.
   */
  def materialize: Events[Events.Reaction[T]] = new Events.Materialize(this)

  /** Creates a new event stream `s` that produces events by consecutively
   *  applying the specified operator `op` to the previous event that `s`
   *  produced and the current event that this event stream value produced.
   *
   *  The `scanPast` operation allows the current event from this event stream to be
   *  mapped into a different event by looking "into the past", i.e. at the
   *  event previously emitted by the resulting event stream.
   *
   *  Example -- assume that an event stream `r` produces events `1`, `2` and
   *  `3`. The following `s`:
   *
   *  {{{
   *  val s = r.scanPast(0)((sum, n) => sum + n)
   *  }}}
   *
   *  will produce events `1`, `3` (`1 + 2`) and `6` (`3 + 3`).
   *  '''Note:''' the initial value `0` is '''not emitted'''.
   *  Shown graphically:
   *
   *  {{{
   *  time     ----------------->
   *  this     --1-----2----3--->
   *  scanPast --1-----3----6--->|
   *  }}}
   *
   *  The `scanPast` can also be used to produce an event stream of a different
   *  type. The following produces a complete history of all the events seen so
   *  far:
   *
   *  {{{
   *  val s2 = r.scanPast(List[Int]()) {
   *    (history, n) => n :: history
   *  }
   *  }}}
   *
   *  The `s2` will produce events `1 :: Nil`, `2 :: 1 :: Nil` and
   *  `3 :: 2 :: 1 :: Nil`.
   *  '''Note:''' the initial value `Nil` is '''not emitted'''.
   *
   *  This operation is closely related to a `scanLeft` on a collection --
   *  if an event stream were a sequence of elements, then `scanLeft` would
   *  produce a new sequence whose elements correspond to the events of the
   *  resulting event stream.
   *
   *  @tparam S        the type of the events in the resulting event stream
   *  @param z         the initial value of the scan past
   *  @param op        the operator the combines the last produced and the
   *                   current event into a new one
   *  @return          an event stream that scans events from `this` event stream
   */
  def scanPast[@spec(Int, Long, Double) S](z: S)(op: (S, T) => S): Events[S] =
    new Events.ScanPast(this, z, op)

  /** Returns a subsequence of events such that subsequent events are not equal.
   */
  def changed(initial: T): Events[T] =
    new Events.Changed(this, initial)

  /** Reduces all the events in this event stream.
   *
   *  Emits a single event *after* the event stream unreacts, and then it unreacts
   *  itself. For example, the event stream `this.reducePast(0)(_ + _)` graphically:
   *
   *  {{{
   *  time       ----------------->
   *  this       --1-----2----3-|
   *  reducePast ---------------6|
   *  }}}
   *
   *  @tparam S        the type of the events in the resulting event stream
   *  @param z         the initial value of the reduce past
   *  @param op        the operator that combines the last event and the current one
   *  @return          an event stream that emits the reduction of all events once
   */
  def reducePast[@spec(Int, Long, Double) S](z: S)(op: (S, T) => S): Events[S] =
    new Events.ReducePast(this, z, op)

  /** Emits the total number of events produced by this event stream.
   *
   *  The returned value is a [[io.reactors.Signal]] that holds the total number of
   *  emitted events.
   *
   *  {{{
   *  time  ---------------->
   *  this  ---x---y--z--|
   *  count ---1---2--3--|
   *  }}}
   *
   *  @return           an event stream that emits the total number of events emitted
   *                    since `card` was called
   */
  def count(implicit dummy: Spec[T]): Events[Int] = new Events.Count[T](this)

  /** Mutates the target mutable event stream called `mutable` each time `this`
   *  event stream produces an event.
   *
   *  Here is an example, given an event stream of type `r`:
   *
   *  {{{
   *  val eventLog = new Events.Mutable(mutable.Buffer[String]())
   *  val eventLogMutations = r.mutate(eventLog) { buffer => event =>
   *    buffer += "at " + System.nanoTime + ": " + event
   *  } // <-- eventLog event propagated
   *  }}}
   *
   *  Whenever an event arrives on `r`, an entry is added to the buffer underlying
   *  `eventLog`. After the mutation completes, a modification event is produced by
   *  the `eventLog` and can be used subsequently:
   *
   *  {{{
   *  val uiUpdates = eventLog onEvent { b =>
   *    eventListWidget.add(b.last)
   *  }
   *  }}}
   *
   *  '''Note:'''
   *  No two events will ever be concurrently processed by different threads on the same
   *  event stream mutable, but an event that is propagated from within the `mutation`
   *  can trigger an event on `this`.
   *  The result is that `mutation` is invoked concurrently on the same thread.
   *  The following code is problematic has a feedback loop in the dataflow graph:
   *
   *  {{{
   *  val emitter = new Events.Emitter[Int]
   *  val mutable = new Events.Mutable[mutable.Buffer[Int]()]
   *  emitter.mutate(mutable) { buffer => n =>
   *    buffer += n
   *    if (n == 0)
   *      emitter.react(n + 1) // <-- event propagated
   *    assert(buffer.last == n)
   *  }
   *  emitter.react(0)
   *  }}}
   *
   *  The statement `emitter.react(n + 1)` in the `mutate` block
   *  suspends the current mutation, calls the mutation
   *  recursively and changes the value of `cell`, and the assertion fails when
   *  the first mutation resumes.
   *
   *  Care must be taken to avoid `f` from emitting events in feedback loops.
   *
   *  @tparam M   the type of the event stream mutable value
   *  @param m    the target mutable stream to be mutated with events from this stream
   *  @param f    the function that modifies `mutable` given an event of
   *              type `T`
   *  @return     a subscription used to cancel this mutation
   */
  def mutate[M >: Null <: AnyRef](m: Events.Mutable[M])(
    f: M => T => Unit
  ): Subscription =
    onReaction(new Events.MutateObserver(m, f))

  /** Mutates multiple mutable event stream values `m1` and `m2` each time that `this`
   *  event stream produces an event.
   *
   *  Note that the objects `m1` and `m2` are mutated simultaneously, and events are
   *  propagated after the mutation ends. This version of the `mutate` works on multiple
   *  event streams.
   *  
   *  @tparam M1          the type of the first mutable event stream
   *  @tparam M2          the type of the second mutable event stream
   *  @param m1          the first mutable stream
   *  @param m2          the second mutable stream
   *  @param f           the function that modifies the mutables
   *  @return            a subscription used to cancel this mutation
   */
  def mutate[M1 >: Null <: AnyRef, M2 >: Null <: AnyRef](
    m1: Events.Mutable[M1], m2: Events.Mutable[M2]
  )(f: (M1, M2) => T => Unit): Subscription =
    onReaction(new Events.Mutate2Observer(m1, m2, f))

  /** Mutates multiple mutable event stream values `m1`, `m2` and `m3` each time that
   *  `this` event stream produces an event.
   *
   *  Note that the objects `m1`, `m2` and `m3` are mutated simultaneously, and events
   *  are propagated after the mutation ends. This version of the `mutate` works on
   *  multiple event streams.
   *  
   *  @tparam M1          the type of the first mutable event stream
   *  @tparam M2          the type of the second mutable event stream
   *  @tparam M3          the type of the third mutable event stream
   *  @param m1          the first mutable stream
   *  @param m2          the second mutable stream
   *  @param m3          the second mutable stream
   *  @param f           the function that modifies the mutables
   *  @return            a subscription used to cancel this mutation
   */
  def mutate[M1 >: Null <: AnyRef, M2 >: Null <: AnyRef, M3 >: Null <: AnyRef](
    m1: Events.Mutable[M1], m2: Events.Mutable[M2], m3: Events.Mutable[M3]
  )(f: (M1, M2, M3) => T => Unit)(implicit dummy: Spec[T]): Subscription =
    onReaction(new Events.Mutate3Observer(m1, m2, m3, f))

  /** Creates a new event stream that produces events from `this` event stream only
   *  after `that` produces an event.
   *
   *  After `that` emits some event, all events from `this` are produced on the
   *  resulting event stream.
   *  If `that` unreacts before an event is produced on `this`, the resulting event\
   *  stream unreacts.
   *  If `this` unreacts, the resulting event stream unreacts.
   *
   *  @tparam S          the type of `that` event stream
   *  @param that        the event stream after whose first event the result can start
   *                     propagating events
   *  @return            the resulting event stream that emits only after `that` emits
   *                     at least once
   */
  def after[@spec(Int, Long, Double) S](that: Events[S]): Events[T] =
    new Events.After[T, S](this, that)

  /** Creates a new event stream value that produces events from `this` event stream
   *  value until `that` produces an event.
   *
   *  If `this` unreacts before `that` produces a value, the resulting event stream
   *  unreacts.
   *  Otherwise, the resulting event stream unreacts whenever `that` produces a
   *  value.
   *
   *  @tparam S         the type of `that` event stream
   *  @param that       the event stream until whose first event the result
   *                    propagates events
   *  @return           the resulting event stream that emits only until `that` emits
   */
  def until[@spec(Int, Long, Double) S](that: Events[S]): Events[T] =
    new Events.Until[T, S](this, that)

  /** Defers events from this stream until first event from the target event stream.
   *
   *  All events from this event stream are kept in a buffer until the first occurrence
   *  of an event in `that` event stream. After that, all events from the buffer are
   *  emitted on the resulting event stream, and the rest of the events are forwarded
   *  normally.
   *
   *  This is shown in the following:
   *
   *  {{{
   *  time   ---------------------->
   *  this   --1---2-------3---4--->
   *  that   --------x-------y---z->
   *  delay  --------1-2---3---4--->
   *  }}}
   *
   *  @tparam S       type of events in `that` event stream
   *  @param that     event stream whose first event flushes the events.
   *  @return
   */
  def defer[@spec(Int, Long, Double) S](that: Events[S])(
    implicit a: Arrayable[T]
  ): Events[T] =
    new Events.Defer[T, S](this, that)

  /** Creates an event stream that forwards an event from this event stream only once.
   *
   *  The resulting event stream emits only a single event produced by `this`
   *  event stream after `once` is called, and then unreacts.
   *
   *  {{{
   *  time ----------------->
   *  this --1-----2----3--->
   *  once      ---2|
   *  }}}
   *
   *  @return           an event stream with the first event from `this`
   */
  def once: Events[T] = new Events.Once[T](this)

  /** After `this` event stream unreacts, the resulting stream emits the last event.
   *
   *  {{{
   *  time ------------------>
   *  this ---1--2----3--|
   *  last --------------3|
   *  }}}
   *
   *  Note: if there were no events in `this` stream by the time it unreacts, the
   *  resulting stream unreacts without emitting anything.
   *
   *  @return           the last event from this event stream
   */
  def last: Events[T] = new Events.Last[T](this)

  /** Filters events from `this` event stream value using a specified predicate `p`.
   *
   *  Only events from `this` for which `p` returns `true` are emitted on the
   *  resulting event stream.
   *
   *  @param p          the predicate used to filter events
   *  @return           an event streams with the filtered events
   */
  def filter(p: T => Boolean): Events[T] = new Events.Filter(this, p)

  /** Filters events from `this` event stream and maps them in the same time.
   *
   *  The `collect` combinator uses a partial function `pf` to filter events
   *  from `this` event stream. Events for which the partial function is defined
   *  are mapped using the partial function, others are discarded.
   *
   *  '''Note:'''
   *  This combinator is defined only for event streams that contain reference events.
   *  You cannot call it for event streams whose events are primitive values, such as
   *  `Int`. This is because the `PartialFunction` class is not itself specialized.
   *
   *  @tparam S         the type of the mapped event stream
   *  @param pf         partial function used to filter and map events
   *  @param evidence   evidence that `T` is a reference type
   *  @return           an event stream with the partially mapped events
   */
  def collect[S <: AnyRef](pf: PartialFunction[T, S])(implicit evidence: T <:< AnyRef):
    Events[S] =
    new Events.Collect(this, pf)

  /** Returns a new stream that maps events from `this` stream using the function `f`.
   *
   *  {{{
   *  time    --------------------->
   *  this    --e1------e2------|
   *  mapped  --f(e1)---f(e2)---|
   *  }}}
   *
   *  @tparam S         the type of the mapped events
   *  @param f          the mapping function
   *  @return           event stream value with the mapped events
   */
  def map[@spec(Boolean, Int, Long, Double) S](f: T => S): Events[S] =
    new Events.Map(this, f)

  /** Whenever `this` stream emits, uses the sampling function to emit another event.
   *
   *  This combinator is useful when there is a clear ordering of events in different
   *  event stream, and the incremental system state needs to be sampled at specific
   *  points in time. The sampling function is guaranteed to be called only once per
   *  each emitted event (however, if there are multiple subscribers to the resulting
   *  event stream, then the sampling function will be called once for each subscriber).
   *
   *  @tparam S         the type of the sampled events
   *  @param f          the sampling function
   *  @return           event stream value with the sampled events
   */
  def sample[@spec(Int, Long, Double) S](f: =>S): Events[S] =
    this.map(x => f)

  /** Returns an event stream that groups events into event stream using a function.
   *
   *  For each unique key returned by the specified function `f`, the resulting event
   *  stream emits a pair with the key and the event stream of values that map to that
   *  key. The resulting event stream unreacts when `this` event stream unreacts. The
   *  nested event streams also unreact when `this` event stream unreacts.
   *
   *  {{{
   *  time            ----------------------------->
   *  this            ---3-------5----4------7--8-->
   *  groupBy(_ % 2)     (1, 3---5-----------7----->)
   *                                  (0, 4-----8-->)
   *  }}}
   *
   *  @tparam K         the type of the keys according to which events are grouped
   *  @param f          the grouping function for the events
   *  @return           event stream that emits keys and associated event streams
   */
  def groupBy[K](f: T => K): Events[(K, Events[T])] =
    new Events.GroupBy(this, f)

  /** Groups adjacent events together into batches.
   *
   *  Batches have the specified size, unless `this` unreacts before sufficiently many
   *  events are batched -- in this case, the last batch may have less events than what
   *  was specified.
   *
   *  '''Note:''' at the moment, this operation is not specialized, and may incur some
   *  boxing when events are primitive elements.
   *
   *  {{{
   *  time       --------------------------------------->
   *  this       -----1---2---3------------4---5--|
   *  batch(3)   -------------[1, 2, 3]--------[4, 5]-|
   *  }}}
   *
   *  @param sz         the size of each batch, must be greater than `0`
   *  @return           event stream with batches of adjacent events
   */
  def batch(sz: Int): Events[Seq[T]] = {
    assert(sz > 0)
    new Events.Batch(this, sz)
  }

  /** Creates a sliding window of the events produced in this event stream.
   *
   *  {{{
   *  time       ------------------------------------------->
   *  this       -----1----2------3----------4---------|
   *  batch(3)   -----[1]--[2,1]--[3,2,1]----[4,3,2]---|
   *  }}}
   *
   *  '''Note:''' whenever an event arrives, the sliding window must be updated.
   *  The sliding window is represented with an immutable queue data structure.
   *  This data structure is used to incrementally a new version of the sliding window.
   *  The update operation takes `O(1)` time, but needs to allocate around 7 objects on
   *  average. That is generally not very expensive, but clients that really need top
   *  performance should use `mutate` with a mutable queue data structure to maintain
   *  the sliding window.
   *
   *  The resulting `Conc.Queue` has `O(log n)` access to elements, where `n` is the
   *  size of the sliding window. It be converted to an array in `O(n)` time.
   *
   *  @param sz      size of the sliding window
   *  @return        the sliding window data structure
   */
  def sliding(sz: Int)(implicit s: Spec[T]): Events[Conc.Queue[T]] = {
    assert(sz > 0)
    new Events.Sliding(this, sz, s)
  }

  /** Returns a new event stream that forwards the events from `this` event stream as
   *  long as they satisfy the predicate `p`.
   *
   *  After an event that does not specify the predicate occurs, the resulting event
   *  stream unreacts.
   *
   *  If the predicate throws an exception, the exceptions is propagated, and the
   *  resulting event stream unreacts.
   *
   *  {{{
   *  time             ------------------------>
   *  this             -0---1--2--3-4--1-5--2-->
   *  takeWhile(_ < 4)     -1--2--3-|
   *  }}}
   *
   *  @param p          the predicate that specifies whether to take the element
   *  @return           event stream with the forwarded events
   */
  def takeWhile(p: T => Boolean): Events[T] = new Events.TakeWhile(this, p)

  /** Returns a new event stream that forwards the events from `this` event stream as
   *  long as they satisfy the predicate `p`.
   *
   *  After an event that does not specify the predicate occurs, the resulting event
   *  stream unreacts.
   *
   *  If the predicate throws an exception, the exceptions is propagated, and the
   *  resulting event stream unreacts.
   *
   *  {{{
   *  time             ------------------------>
   *  this             -0---1--2--3-4--1-5--2-->
   *  dropWhile(_ < 4)     ---------4--1-5--2-->
   *  }}}
   *
   *  @param p          the predicate that specifies whether to take the element
   *  @return           event stream with the forwarded events
   */
  def dropWhile(p: T => Boolean): Events[T] = new Events.DropWhile(this, p)

  /** Drop all events after an event that satisfies a predicate.
   *
   *  This is similar to `takeWhile`, but includes the event that satisfies the
   *  predicate.
   *
   *  {{{
   *  time                ------------------------>
   *  this                -0---1--2--3-4--1-5--2-->
   *  dropAfter(_ == 4)       -1--2--3-4|
   *  }}}
   *
   *  @param p          the predicate that specifies whether to drop subsequent events
   *  @return           event stream with the forwarded events
   */
  def dropAfter(p: T => Boolean): Events[T] = new Events.DropAfter(this, p)

  /** Takes `n` events from this event stream, and unreacts.
   *
   *  @param n          number of events to take
   *  @return           event stream with the forwarded events
   */
  def take(n: Int): Events[T] =
    if (n > 0) new Events.Take(this, n)
    else new Events.Never[T]

  /** Drops `n` events from this event stream, and emits the rest.
   *
   *  @param n          number of events to drop
   *  @return           event stream with the forwarded events
   */
  def drop(n: Int): Events[T] = new Events.Drop(this, n)

  /** Emits all the events from this even stream except the first one.
   *
   *  @return           event stream with the forwarded events
   */
  def tail: Events[T] = drop(1)

  /** Returns events from the last event stream that `this` emitted as an
   *  event of its own, in effect multiplexing the nested reactives.
   *
   *  The resulting event stream only emits events from the event stream last
   *  emitted by `this`, the preceding event streams are ignored.
   *
   *  This combinator is only available if this event stream emits events
   *  that are themselves event streams.
   *
   *  Example:
   *
   *  {{{
   *  val currentEvents = new Events.Emitter[Events[Int]]
   *  val e1 = new Events.Emitter[Int]
   *  val e2 = new Events.Emitter[Int]
   *  val currentEvent = currentEvents.mux()
   *  val prints = currentEvent.onEvent(println)
   *
   *  currentEvents.react(e1)
   *  e2.react(1) // nothing is printed
   *  e1.react(2) // 2 is printed
   *  currentEvents.react(e2)
   *  e2.react(6) // 6 is printed
   *  e1.react(7) // nothing is printed
   *  }}}
   *
   *  Shown on the diagram:
   *
   *  {{{
   *  time            ------------------->
   *  currentEvents   --e1------e2------->
   *  e1              --------2----6----->
   *  e2              -----1----------7-->
   *  currentEvent    --------2----6----->
   *  }}}
   *
   *  '''Use case:'''
   *
   *  {{{
   *  def mux[S](): Events[S]
   *  }}}
   *
   *  @tparam S          the type of the events in the nested event stream
   *  @param evidence    an implicit evidence that `this` event stream is nested -- it
   *                     emits events of type `T` that is actually an `Events[S]`
   *  @return            event stream of events from the event stream last emitted by
   *                     `this`
   */
  def mux[@spec(Int, Long, Double) S](
    implicit evidence: T <:< Events[S], ds: Spec[S]
  ): Events[S] =
    new Events.Mux[T, S](this, evidence)

  /** Returns a new event stream that emits an event when this event stream unreacts.
   *
   *  After the current event stream unreacts, the result event stream first emits an
   *  event of type `Unit`, and then unreacts itself.
   *
   *  Exceptions from this event stream are propagated until the resulting event stream
   *  unreacts -- after that, `this` event stream is not allowed to produce exceptions.
   *
   *  Shown on the diagram:
   *
   *  {{{
   *  time            ------------------->
   *  this            --1--2-----3-|
   *  currentEvent    -------------()-|
   *  }}}
   *
   *  @return           the unreaction event stream and subscription
   */
  def done(implicit ds: Spec[T]): Events[Unit] = new Events.Unreacted(this)

  /** Creates a union of `this` and `that` event stream.
   *
   *  The resulting event stream emits events from both `this` and `that`
   *  event stream.
   *  It unreacts when both `this` and `that` event stream unreact.
   *
   *  @param that      another event stream for the union
   *  @return          the event stream with unified events from `this` and `that`
   */
  def union(that: Events[T]): Events[T] = new Events.Union(this, that)

  /** Unifies the events produced by all the event streams emitted by `this`.
   *
   *  This operation is only available for event stream values that emit
   *  other event streams as events.
   *  The resulting event stream unifies events of all the event streams emitted by
   *  `this`. Once `this` and all the event streams emitted by `this` unreact, the
   *  resulting event stream terminates.
   *
   *  '''Note:''' if the same event stream is emitted multiple times, it will be
   *  subscribed to multiple times.
   *
   *  Example:
   *
   *  {{{
   *  time  -------------------------->
   *  this     --1----2--------3------>
   *               ---------5----6---->
   *                 ---4----------7-->
   *  union -----1----2-4---5--3-6-7-->
   *  }}}
   *
   *  '''Use case:'''
   *
   *  {{{
   *  def union[S](): Events[S]
   *  }}}
   *
   *  @tparam S         the type of the events in event streams emitted by `this`
   *  @param evidence   evidence that events of type `T` produced by `this`
   *                    are actually event stream values of type `S`
   *  @return           the event stream with the union of all the events from the
   *                    nested event streams
   */
  def union[@spec(Int, Long, Double) S](
    implicit evidence: T <:< Events[S], ds: Spec[S]
  ): Events[S] =
    new Events.PostfixUnion[T, S](this, evidence)

  /** Alias for `union`.
   */
  def flatten[@spec(Int, Long, Double) S](
    implicit evidence: T <:< Events[S], ds: Spec[S]
  ): Events[S] =
    union[S]

  /** Creates a concatenation of `this` and `that` event stream.
   *
   *  The resulting event stream produces all the events from `this`
   *  event stream until `this` unreacts, and then outputs all the events from
   *  `that` that happened before and after `this` unreacted.
   *  To do this, this operation potentially caches all the events from
   *  `that`.
   *  When `that` unreacts, the resulting event stream unreacts.
   *
   *  '''Use case:'''
   *
   *  {{{
   *  def concat(that: Events[T]): Events[T]
   *  }}}
   *
   *  '''Note:''' This operation potentially caches events from `that`.
   *  Unless certain that `this` eventually unreacts, `concat` should not be used.
   *
   *  @param that      another event stream for the concatenation
   *  @param a         evidence that arrays can be created for the type `T`
   *  @return          event stream that concatenates events from `this` and `that`
   */
  def concat(that: Events[T])(implicit a: Arrayable[T]): Events[T] =
    new Events.Concat(this, that)

  /** Concatenates the events produced by all the event streams emitted by `this`.
   *
   *  This operation is only available for event stream values that emit
   *  other event streams as events.
   *  Once `this` and all the event streams unreact, this event stream unreacts.
   *
   *  '''Use case:'''
   *
   *  {{{
   *  def concat[S](): Events[S]
   *  }}}
   *
   *  '''Note:''' This operation potentially buffers events from the nested
   *  event streams.
   *  Unless each event stream emitted by `this` is known to unreact eventually,
   *  this operation should not be called.
   *
   *  @tparam S         the type of the events in event streams emitted by `this`
   *  @param evidence   evidence that events of type `T` produced by `this`
   *                    are actually event stream values of type `S`
   *  @param a          evidence that arrays can be created for type `S`
   *  @return           the event stream that concatenates all the events from nested
   *                    event streams
   */
  def concat[@spec(Int, Long, Double) S](
    implicit evidence: T <:< Events[S], a: Arrayable[S]
  ): Events[S] =
    new Events.PostfixConcat[T, S](this, evidence, a)

  /** Returns an event stream that forwards from the first active nested event stream.
   *
   *  Regardless of the order in which the nested event streams were emitted, only the
   *  nested event stream that is the first to emit an event gets chosen.
   *
   *  This is illustrated in the following, where the second event stream in `this` is
   *  the first to emit an event.
   *
   *  {{{
   *  time   --------------------------->
   *  this       ------4--7---11-------->
   *               --1------2-----3----->
   *                   --------0---5---->
   *  first  --------1------1-----3----->
   *  }}}
   *
   *  @tparam S         the type of the events in event stream emitted by `this`
   *  @param evidence   evidence that events of type `T` produced by `this`
   *                    are actually event streams of type `S`
   *  @return           event stream that concatenates all the events from nested
   *                    event streams
   */
  def first[@spec(Int, Long, Double) S](implicit evidence: T <:< Events[S]): Events[S] =
    new Events.PostfixFirst[T, S](this, evidence)

  /** Syncs the arrival of events from `this` and `that` event stream.
   *
   *  Ensures that pairs of events from this event stream and that event stream
   *  are emitted together.
   *  If the events produced in time by `this` and `that`, the sync will be as
   *  follows:
   *
   *  {{{
   *  time   --------------------------->
   *  this   ----1---------2-------4---->
   *  that   --1-----2--3--------------->
   *  sync   ----1,1-------2,2-----4,3-->
   *  }}}
   *
   *  Pairs of events produced from `this` and `that` are then transformed
   *  using specified function `f`.
   *  For example, clients that want to output tuples do:
   *
   *  {{{
   *  val synced = (a sync b) { (a, b) => (a, b) }
   *  }}}
   *
   *  Clients that, for example, want to create differences in pairs of events
   *  do:
   *
   *  {{{
   *  val diffs = (a sync b)(_ - _)
   *  }}}
   *
   *  The resulting event stream unreacts either when
   *  `this` unreacts and there are no more buffered events from this,
   *  or when `that` unreacts and there are no more buffered events from
   *  `that`.
   *
   *  '''Use case:'''
   *
   *  {{{
   *  def sync[S, R](that: Events[S])(f: (T, S) => R): Events[R]
   *  }}}
   *
   *  '''Note:''' This operation potentially buffers events from `this` and `that`.
   *  Unless certain that both `this` produces a bounded number of events
   *  before the `that` produces an event, and vice versa, this operation
   *  should not be called.
   *
   *  @tparam S         the type of the events in `that` event stream
   *  @tparam R         the type of the events in the resulting event stream
   *  @param that       the event stream to sync with
   *  @param f          the mapping function for the pair of events
   *  @param at         evidence that arrays can be created for the type `T`
   *  @param as         evidence that arrays can be created for the type `S`
   *  @return           the event stream with the resulting events
   */
  def sync[@spec(Int, Long, Double) S, @spec(Int, Long, Double) R](that: Events[S])(
    f: (T, S) => R
  )(implicit at: Arrayable[T], as: Arrayable[S]): Events[R] =
    new Events.Sync[T, S, R](this, that, f)

  /** Reverses the events of this event stream.
   *
   *  The events are emitted in the opposite order from what they are emitted on `this`
   *  event stream. Exceptions are simply piped through in the order in which they
   *  come in.
   *
   *  {{{
   *  time      ------------------------->
   *  this      ------1----2-3---|
   *  reverse   -----------------3-2-1-|
   *  }}}
   *
   *  '''Note:''' This operation buffers events from `this` event stream until `this`
   *  event stream unreacts. No events are emitted before `this` unreacts. Consequently,
   *  the resulting event stream may buffer events indefinitely, resulting in a memory
   *  leak. Use this operation **only if you can guarantee that the current event
   *  stream is finite**.
   */
  def reverse(implicit a: Arrayable[T]): Events[T] = new Events.Reverse[T](this)

  /** Forwards an event from this event stream with some probability.
   *
   *  The probability is specified as a real value from 0.0 to 1.0.
   *
   *  @param probability    the probability to forward an event
   *  @return               the event stream that forwards events with some probability
   */
  def possibly(probability: Double): Events[T] = new Events.Possibly(this, probability)

  /** Zips values from this event stream with the hint value.
   */
  def zipHint[@spec(Int, Long, Double) S](f: (T, Any) => S): Events[S] =
    new Events.ZipHint(this, f)

  /** Collects values from the event stream by applying a partial function, if possible.
   */
  def collectHint[W](pf: PartialFunction[Any, W]): Events[T] =
    new Events.CollectHint(this, pf)

  /** Converts an event stream of `Events[T]` to type `Events[Try[T]]`.
   *
   *  Inbound exceptions are lifted into `Failure` events, while normal events are
   *  converted into `Success` events.
   */
  def liftTry: Events[Try[T]] =
    new Events.LiftTry(this)

  /** Converts an event stream of `Events[Try[S]]` to type `Events[S]`.
   *
   *  Normal events are emitted for `Success` objects, and exceptions for `Failure`.
   */
  def unliftTry[S](implicit evid: T <:< Try[S]): Events[S] =
    new Events.UnliftTry(this, evid)

  /** Incrementally computes state, and emits events to an observer.
   *
   *  Creates an incrementally updated state, and uses it to emit events to an observer
   *  whenever `this` event stream emits an event.
   *
   *  @tparam S        type of the output events
   *  @param state     function that creates some incrementally computed state, and
   *                   returns a tuple of the subscription for that state, and the
   *                   function that emits events from this state
   *  @return          an event stream that emits a sampled view of the state whenever
   *                   `this` event stream emits an event
   */
  def incremental[@spec(Int, Long, Double) S](
    state: =>(Subscription, Observer[S] => Unit)
  )(implicit s: Spec[S]): Events[S] = {
    new Events.Incremental(this, () => state)
  }
  
  /** Pushes farther every `count` value.
   *
   *  If `count` is set to `2`, result will be as follows:
   *
   *  {{{
   *  time   ----------------------------->
   *  this   ----1--2---3----4-------5---->
   *  that   ----1------3------------5---->
   *  }}}
   *
   */
  def each(count: Int): Events[T] = {
    new Events.Each[T](this, count)
  }

  /** Repeat each value every `count` times.
   *
   *  Assumed of shared state between repeated values.
   *  If there is a need of separate states, e.g. for
   *  mutable objects, consider implementing the `copy` method.
   *
   *  If `count` is set to `2`, result will be as follows:
   *
   *  {{{
   *  time   --------------------------------->
   *  this   ----1-----2-----3------4----5---->
   *  that   ----1-1---2--2--3-3----4-4--5-5-->
   *  }}}
   */
  def repeat(count: Int)(copy: T => T = state => state): Events[T] = {
    new Events.Repeat[T](this, count, copy)
  }
  
  /** Partitions this events stream in two events streams according to a predicate.
   * 
   *  @return a pair of the first events stream consists of all elements that
   *          satisfy the predicate `p`, and the second event stream consists
   *          of all elements that don't. The relative order of the elements
   *          in the resulting events streams is the same as in the original.
   */
  def partition(p: T => Boolean): (Events[T], Events[T]) = {
    val trueEmitter = new Events.Emitter[T]
    val falseEmitter = new Events.Emitter[T]

    this.onReaction(new Events.PartitionObserver[T](trueEmitter, falseEmitter, p))
    (trueEmitter, falseEmitter)
  }

  /** Converts this event stream into a `Signal`.
   *
   *  The resulting signal initially does not contain an event,
   *  and subsequently contains any event that `this` event stream produces.
   *
   *  @return          the signal version of the current event stream
   */
  def toEmpty: Signal[T] =
    new Events.ToSignal(this, false, null.asInstanceOf[T])

  /** Same as `toEmpty`, but emits an event on subscription if signal is non-empty.
   */
  def toEager: Signal[T] =
    new Events.ToSignal(this, false, null.asInstanceOf[T])

  /** Given an initial event `init`, converts this event stream into a `Signal`.
   *
   *  The resulting signal initially contains the event `init`,
   *  and subsequently any event that `this` event stream produces.
   *
   *  @param init      an initial value for the signal
   *  @return          the signal version of the current event stream
   */
  def toSignal(init: T): Signal[T] =
    new Events.ToSignal(this, true, init)

  /** Given an initial event `init`, converts the event stream into a cold `Signal`.
   *
   *  Cold signals emit events only when some observer is subscribed to them.
   *  As soon as there are no subscribers for the signal, the signal unsubscribes itself
   *  from its source event stream. While unsubscribed, the signal **does not update its
   *  value**, even if its event source (`this` event stream) emits events.
   *
   *  If there is at least one subscription to the cold signal, the signal subscribes
   *  itself to its event source (`this` event stream) again.
   *
   *  The `unsubscribe` method on the resulting signal does nothing -- the subscription
   *  of the cold signal unsubscribes only after all of the subscribers unsubscribe, or
   *  the source event stream unreacts.
   */
  def toCold(init: T): Signal[T] = new Events.ToColdSignal(this, init)

  /** Returns a signal that becomes `true` when this event stream is done.
   */
  def toDoneSignal: Signal[Boolean] = this.done.map(_ => true).toSignal(false)

  /** Streams events from this event stream into an event buffer.
   *
   *  Clients must manually call `dequeue` on the resulting event buffer when they
   *  are ready to release events.
   *
   *  @return          a new event buffer with all the events from this event stream
   */
  def toEventBuffer(implicit a: Arrayable[T]): EventBuffer[T] = {
    val buffer = new EventBuffer[T]
    buffer.subscription = this onEvent { x =>
      buffer.enqueue(x)
    }
    buffer
  }

  /** Returns the first event emitted by this event stream.
   *
   *  This method will return immediately and will not block.
   *
   *  This method will return a value only if this event stream emits one or more values
   *  on subscription. Otherwise, this method throws a `NoSuchElementException`.
   */
  def get: T = {
    val sig = this.once.toEmpty
    sig.unsubscribe()
    sig()
  }

  /** Pipes the events on this input stream to the target channel.
   *
   *  Exceptions are ignored.
   */
  def pipe(ch: Channel[T]): Subscription = this.ignoreExceptions.onEvent(x => ch ! x)

  /** Creates an `IVar` event stream value, completed with the first event from
   *  this event stream.
   *
   *  After the `IVar` is assigned, all subsequent events are ignored.
   *  If the `self` event stream is unreacted before any event arrives, the
   *  `IVar` is closed.
   *
   *  @return          an `IVar` with the first event from this event stream
   */
  def toIVar: IVar[T] = {
    val iv = new IVar[T]
    val obs = new Events.ToIVar(iv)
    obs.subscription = onReaction(obs)
    iv
  }

  /** Creates an initially empty `RCell`, updated with events of this event stream.
   *
   *  After the first event gets produced, the `RCell` is assigned this value, and is
   *  from there on not empty. The `RCell` can also, alternatively, be modified by
   *  clients.
   *
   *  @return          an `RCell` with the first event from this event stream
   */
  def toRCell: RCell[T] = {
    val c = new RCell[T](null.asInstanceOf[T], false, Subscription.empty)
    val obs = new Events.ToRCell(c)
    c.subscription = this.onReaction(obs)
    c
  }

}


/** Contains useful `Events` implementations and factory methods.
 */
object Events {
  private val bufferUpperBound = 8

  private val hashTableLowerBound = 5

  sealed trait Reaction[+T]

  case class React[+T](x: T) extends Reaction[T]

  case class Except[+T](t: Throwable) extends Reaction[T]

  case object Unreact extends Reaction[Nothing]

  /** The default implementation of a event stream value.
   *
   *  Keeps an optimized weak collection of weak references to subscribers.
   *  References to subscribers that are no longer reachable in the application
   *  will be removed eventually.
   *
   *  @tparam T       type of the events in this event stream value
   */
  trait Push[@spec(Int, Long, Double) T] extends Events[T] {
    private[reactors] var propagationDepth = 0
    private[reactors] var demux: AnyRef = null
    private[reactors] var eventsUnreacted: Boolean = false
    def onReaction(observer: Observer[T]): Subscription = {
      if (eventsUnreacted) {
        observer.unreact()
        Subscription.empty
      } else {
        demux match {
          case null =>
            demux = new Ref(observer)
          case w: Ref[Observer[T] @unchecked] =>
            val wb = new FastBuffer[Observer[T]]
            wb.addRef(w)
            wb.addEntry(observer)
            demux = wb
          case wb: FastBuffer[Observer[T] @unchecked] =>
            if (wb.size < bufferUpperBound) {
              wb.addEntry(observer)
            } else {
              val wht = toHashTable(wb)
              wht.addEntry(observer)
              demux = wht
            }
          case wht: FastHashTable[Observer[T] @unchecked] =>
            wht.addEntry(observer)
        }
        newSubscription(observer)
      }
    }
    private def newSubscription(r: Observer[T]) = new Subscription {
      def unsubscribe() {
        removeReaction(r)
      }
    }
    private def removeReaction(r: Observer[T]) {
      demux match {
        case null =>
          // nothing to invalidate
        case w: Ref[Observer[T] @unchecked] =>
          if (w.get eq r) w.clear()
        case wb: FastBuffer[Observer[T] @unchecked] =>
          wb.invalidateEntry(r)
        case wht: FastHashTable[Observer[T] @unchecked] =>
          wht.invalidateEntry(r)
      }
    }
    protected[reactors] def reactAll(value: T, hint: Any) {
      propagationDepth += 1
      try {
        demux match {
          case null =>
            // no need to inform anybody
          case w: Ref[Observer[T] @unchecked] =>
            val r = w.get
            if (r != null) r.react(value, hint)
            else demux = null
          case wb: FastBuffer[Observer[T] @unchecked] =>
            bufferReactAll(wb, value, hint)
          case wht: FastHashTable[Observer[T] @unchecked] =>
            tableReactAll(wht, value, hint)
        }
      } finally {
        propagationDepth -= 1
      }
    }
    protected[reactors] def exceptAll(t: Throwable) {
      propagationDepth += 1
      try {
        demux match {
          case null =>
            // no need to inform anybody
          case w: Ref[Observer[T] @unchecked] =>
            val r = w.get
            if (r != null) r.except(t)
            else demux = null
          case wb: FastBuffer[Observer[T] @unchecked] =>
            bufferExceptAll(wb, t)
          case wht: FastHashTable[Observer[T] @unchecked] =>
            tableExceptAll(wht, t)
        }
      } finally {
        propagationDepth -= 1
      }
    }
    protected[reactors] def unreactAll() {
      propagationDepth += 1
      try {
        eventsUnreacted = true
        demux match {
          case null =>
            // no need to inform anybody
          case w: Ref[Observer[T] @unchecked] =>
            val r = w.get
            if (r != null) r.unreact()
            else demux = null
          case wb: FastBuffer[Observer[T] @unchecked] =>
            bufferUnreactAll(wb)
          case wht: FastHashTable[Observer[T] @unchecked] =>
            tableUnreactAll(wht)
        }
      } finally {
        propagationDepth -= 1
      }
    }
    private[reactors] def hasSubscriptions: Boolean = {
      demux match {
        case null => false
        case w: Ref[Observer[T] @unchecked] => w.get != null
        case _ => true
      }
    }
    private def checkBuffer(wb: FastBuffer[Observer[T]]) {
      if (wb.size <= 1) {
        if (wb.size == 1) demux = new Ref(wb(0))
        else if (wb.size == 0) demux = null
      }
    }
    private def bufferReactAll(wb: FastBuffer[Observer[T]], value: T, hint: Any) {
      val array = wb.array
      var until = wb.size
      var i = 0
      while (i < until) {
        val ref = array(i)
        val r = ref.get
        if (r ne null) {
          r.react(value, hint)
          i += 1
        } else if (propagationDepth == 1) {
          wb.removeEntryAt(i)
          until -= 1
        }
      }
      if (propagationDepth == 1) checkBuffer(wb)
    }
    private def bufferExceptAll(wb: FastBuffer[Observer[T]], t: Throwable) {
      val array = wb.array
      var until = wb.size
      var i = 0
      while (i < until) {
        val ref = array(i)
        val r = ref.get
        if (r ne null) {
          r.except(t)
          i += 1
        } else if (propagationDepth == 1) {
          wb.removeEntryAt(i)
          until -= 1
        }
      }
      if (propagationDepth == 1) checkBuffer(wb)
    }
    private def bufferUnreactAll(wb: FastBuffer[Observer[T]]) {
      val array = wb.array
      var until = wb.size
      var i = 0
      while (i < until) {
        val ref = array(i)
        val r = ref.get
        if (r ne null) {
          r.unreact()
          i += 1
        } else if (propagationDepth == 1) {
          wb.removeEntryAt(i)
          until -= 1
        } else {
          i += 1
        }
      }
      if (propagationDepth == 1) checkBuffer(wb)
    }
    private def toHashTable(wb: FastBuffer[Observer[T]]) = {
      val wht = new FastHashTable[Observer[T]]
      val array = wb.array
      val until = wb.size
      var i = 0
      while (i < until) {
        val r = array(i).get
        if (r != null) wht.addEntry(r)
        i += 1
      }
      wht
    }
    private def toBuffer(wht: FastHashTable[Observer[T]]) = {
      val wb = new FastBuffer[Observer[T]](bufferUpperBound)
      val table = wht.table
      var i = 0
      while (i < table.length) {
        var ref = table(i)
        if (ref != null && ref.get != null) wb.addRef(ref)
        i += 1
      }
      wb
    }
    private def cleanHashTable(wht: FastHashTable[Observer[T]]) {
      val table = wht.table
      var i = 0
      while (i < table.length) {
        val ref = table(i)
        if (ref ne null) {
          val r = ref.get
          if (r eq null) wht.removeEntryAt(i, null)
        }
        i += 1
      }
    }
    private def checkHashTable(wht: FastHashTable[Observer[T]]) {
      if (wht.size < hashTableLowerBound) {
        val wb = toBuffer(wht)
        demux = wb
        checkBuffer(wb)
      }
    }
    private def tableReactAll(wht: FastHashTable[Observer[T]], value: T, hint: Any) {
      val table = wht.table
      var i = 0
      while (i < table.length) {
        val ref = table(i)
        if (ref ne null) {
          val r = ref.get
          if (r ne null) r.react(value, hint)
        }
        i += 1
      }
      if (propagationDepth == 1) {
        cleanHashTable(wht)
        checkHashTable(wht)
      }
    }
    private def tableExceptAll(wht: FastHashTable[Observer[T]], t: Throwable) {
      val table = wht.table
      var i = 0
      while (i < table.length) {
        val ref = table(i)
        if (ref ne null) {
          val r = ref.get
          if (r ne null) r.except(t)
        }
        i += 1
      }
      if (propagationDepth == 1) {
        cleanHashTable(wht)
        checkHashTable(wht)
      }
    }
    private def tableUnreactAll(wht: FastHashTable[Observer[T]]) {
      val table = wht.table
      var i = 0
      while (i < table.length) {
        val ref = table(i)
        if (ref ne null) {
          val r = ref.get
          if (r ne null) r.unreact()
        }
        i += 1
      }
      if (propagationDepth == 1) {
        cleanHashTable(wht)
        checkHashTable(wht)
      }
    }
  }

  private[reactors] class PushSource[@spec(Int, Long, Double) T] extends Push[T]

  /** Event source that emits events when `react`, `except` or `unreact` is called.
   *
   *  Emitter is simultaneously an event stream, and an observer.
   */
  class Emitter[@spec(Int, Long, Double) T]
  extends Push[T] with Events[T] with Observer[T] {
    private var closed = false
    def react(x: T): Unit = react(x, null)
    def react(x: T, hint: Any): Unit = if (!closed) {
      reactAll(x, hint)
    }
    def except(t: Throwable) = if (!closed) {
      exceptAll(t)
    }
    def unreact() = if (!closed) {
      closed = true
      unreactAll()
      demux = null
    }
  }

  /** An event stream that emits events when the underlying mutable object is modified.
   *
   *  An event with underlying mutable value is emitted whenever the mutable value was
   *  potentially mutated. This type of a signal provides a controlled way of
   *  manipulating mutable values.
   *
   *  '''Note:'''
   *  The underlying mutable object must '''never''' be mutated directly by accessing
   *  the value of the signal and changing the mutable object. Instead, the `mutate`
   *  operation of `Events` should be used to mutate the underlying mutable object.
   *
   *  Example:
   *
   *  {{{
   *  val systemMessages = new Events.Emitter[String]
   *  val log = new Events.Mutable(new mutable.ArrayBuffer[String])
   *  val logMutations = systemMessages.mutate(log) { buffer => msg =>
   *    buffer += msg
   *  }
   *  systemMessages.react("New message arrived!") // buffer now contains the message
   *  }}}
   *
   *  As long as there are no feedback loops in the dataflow graph,
   *  the same thread will never modify the mutable object at the same time.
   *  See the `mutate` method on `Events`s for more information.
   *
   *  Note that mutable event stream never unreacts.
   *
   *  @see [[io.reactors.Events]]
   *  @tparam M          the type of the underlying mutable object
   *  @param content     the mutable object
   */
  class Mutable[M >: Null <: AnyRef](private[reactors] val content: M)
  extends Push[M] with Events[M]

  /** A class for event streams that never emit events.
   *
   *  Subscribers immediately unreact.
   *
   *  @tparam T         type of events never emitted by this event stream
   */
  class Never[@spec(Int, Long, Double) T]
  extends Events[T] {
    def onReaction(obs: Observer[T]) = {
      obs.unreact()
      Subscription.empty
    }
  }

  /** Creates a constant event stream, which always yields the same events.
   */
  def apply[@spec(Int, Long, Double) T](x: T): Events[T] = new Signal.Const(x)

  /** Factory method for creating `mux` event streams.
   *
   *  See `mux` on `Events` for more details.
   */
  def mux[@spec(Int, Long, Double) T](e: Events[Events[T]]): Events[T] =
    e.mux[T]

  /** Factory method for creating `union` event streams.
   *
   *  See `union` on `Events` for more details.
   */
  def union[@spec(Int, Long, Double) T](e: Events[Events[T]]): Events[T] =
    e.union[T]

  /** Returns an event stream that never emits.
   */
  def never[@spec(Int, Long, Double) T]: Events[T] = new Events.Never[T]

  /** Synchronizes a sequence of event streams.
   *
   *  The resulting event stream emits a sequence of events every time it manages
   *  to obtain a sequence from each of the input.
   */
  def sync[@spec(Int, Long, Double) T](es: Events[T]*)(
    implicit a: Arrayable[T]
  ): Events[Seq[T]] = new Events.SyncMany(es)

  def single[@spec(Int, Long, Double) T](x: T): Events[T] = new Events.Single(x)

  private[reactors] class Single[@spec(Int, Long, Double) T](val x: T)
  extends Events[T] {
    def onReaction(obs: Observer[T]): Subscription = {
      obs.react(x, null)
      obs.unreact()
      Subscription.empty
    }
  }

  private[reactors] class MutateObserver[
    @spec(Int, Long, Double) T, M >: Null <: AnyRef
  ](val target: Mutable[M], f: M => T => Unit) extends Observer[T] {
    val mutation = f(target.content)
    def react(x: T, hint: Any) = {
      try mutation(x)
      catch {
        case NonLethal(t) => target.exceptAll(t)
      }
      target.reactAll(target.content, null)
    }
    def except(t: Throwable) = target.exceptAll(t)
    def unreact() = {}
  }

  private[reactors] class Mutate2Observer[
    @spec(Int, Long, Double) T, M1 >: Null <: AnyRef, M2 >: Null <: AnyRef
  ](val t1: Mutable[M1], val t2: Mutable[M2], f: (M1, M2) => T => Unit)
  extends Observer[T] {
    val mutation = f(t1.content, t2.content)
    def react(x: T, hint: Any) = {
      try mutation(x)
      catch {
        case NonLethal(t) =>
          t1.exceptAll(t)
          t2.exceptAll(t)
      }
      t1.reactAll(t1.content, null)
      t2.reactAll(t2.content, null)
    }
    def except(t: Throwable) = {
      t1.exceptAll(t)
      t2.exceptAll(t)
    }
    def unreact() = {}
  }

  private[reactors] class Mutate3Observer[
    @spec(Int, Long, Double) T,
    M1 >: Null <: AnyRef, M2 >: Null <: AnyRef, M3 >: Null <: AnyRef
  ](
    val t1: Mutable[M1], val t2: Mutable[M2], val t3: Mutable[M3],
    f: (M1, M2, M3) => T => Unit
  ) extends Observer[T] {
    val mutation = f(t1.content, t2.content, t3.content)
    def react(x: T, hint: Any) = {
      try mutation(x)
      catch {
        case NonLethal(t) =>
          t1.exceptAll(t)
          t2.exceptAll(t)
          t3.exceptAll(t)
      }
      t1.reactAll(t1.content, null)
      t2.reactAll(t2.content, null)
      t3.reactAll(t3.content, null)
    }
    def except(t: Throwable) = {
      t1.exceptAll(t)
      t2.exceptAll(t)
      t3.exceptAll(t)
    }
    def unreact() = {}
  }

  private[reactors] class OnEventOrDone[@spec(Int, Long, Double) T](
    val reactFunc: T => Unit, val unreactFunc: () => Unit
  ) extends Observer[T] {
    def react(x: T, hint: Any) = reactFunc(x)
    def except(t: Throwable) = throw UnhandledException(t)
    def unreact() = unreactFunc()
  }

  private[reactors] class On[@spec(Int, Long, Double) T](
    val reactFunc: () => Unit
  ) extends Observer[T] {
    def react(x: T, hint: Any) = reactFunc()
    def except(t: Throwable) = throw UnhandledException(t)
    def unreact() = {}
  }

  private[reactors] class OnDone[@spec(Int, Long, Double) T](
    val unreactFunc: () => Unit
  ) extends Observer[T] {
    def react(x: T, hint: Any) = {}
    def except(t: Throwable) = throw UnhandledException(t)
    def unreact() = unreactFunc()
  }

  private[reactors] class Recover[T, U >: T](
    val self: Events[T],
    val pf: PartialFunction[Throwable, U],
    val evid: U <:< AnyRef
  ) extends Events[U] {
    def onReaction(observer: Observer[U]): Subscription =
      self.onReaction(new RecoverObserver(observer, pf, evid))
  }

  private[reactors] class RecoverObserver[T, U >: T](
    val target: Observer[U],
    val pf: PartialFunction[Throwable, U],
    val evid: U <:< AnyRef
  ) extends Observer[T] {
    def react(value: T, hint: Any) {
      target.react(value, hint)
    }
    def except(t: Throwable) {
      val isDefined = try {
        pf.isDefinedAt(t)
      } catch {
        case other if isNonLethal(other) =>
          target.except(other)
          return
      }
      if (!isDefined) target.except(t)
      else {
        val event = try {
          pf(t)
        } catch {
          case other if isNonLethal(other) =>
            target.except(other)
            return
        }
        target.react(event, null)
      }
    }
    def unreact() {
      target.unreact()
    }
  }

  private[reactors] class Materialize[T](
    val self: Events[T]
  ) extends Events[Reaction[T]] {
    def onReaction(observer: Observer[Reaction[T]]): Subscription = {
      self.onReaction(new MaterializeObserver(observer))
    }
  }

  private[reactors] class MaterializeObserver[T](
    val target: Observer[Reaction[T]]
  ) extends Observer[T] {
    def react(value: T, hint: Any): Unit = {
      target.react(React(value), hint)
    }
    def except(t: Throwable): Unit = {
      target.react(Except(t), null)
    }
    def unreact(): Unit = {
      target.react(Unreact, null)
    }
  }

  private[reactors] class IgnoreExceptions[@spec(Int, Long, Double) T](
    val self: Events[T]
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription =
      self.onReaction(new IgnoreExceptionsObserver(observer))
  }

  private[reactors] class IgnoreExceptionsObserver[@spec(Int, Long, Double) T](
    val target: Observer[T]
  ) extends Observer[T] {
    def react(value: T, hint: Any) {
      target.react(value, hint)
    }
    def except(t: Throwable) {
    }
    def unreact() {
      target.unreact()
    }
  }

  private[reactors] class SyncMany[@spec(Int, Long, Double) T](
    val es: Seq[Events[T]]
  )(implicit val a: Arrayable[T]) extends Events[Seq[T]] {
    def newBuffers(self: SyncMany[T]): Seq[UnrolledRing[T]] =
      for (e <- es) yield new UnrolledRing[T]
    def newSyncManyObserver(
      target: Observer[Seq[T]], r: UnrolledRing[T], rs: Array[UnrolledRing[T]],
      subs: Subscription.Collection
    ) = {
      new SyncManyObserver(target, r, rs, subs, new Subscription.Cell)
    }
    def onReaction(target: Observer[Seq[T]]): Subscription = {
      val subs = new Subscription.Collection
      val rs = newBuffers(this).toArray
      val obss = for (r <- rs) yield newSyncManyObserver(target, r, rs, subs)
      for ((e, obs) <- es zip obss) {
        val s = e.onReaction(obs)
        subs.addAndGet(s)
        obs.subscription.set(s)
      }
      subs
    }
  }

  private[reactors] class SyncManyObserver[@spec(Int, Long, Double) T](
    val target: Observer[Seq[T]],
    val buffer: UnrolledRing[T],
    val buffers: Array[UnrolledRing[T]],
    val allSubscriptions: Subscription.Collection,
    val subscription: Subscription.Cell
  ) extends Observer[T] {
    var done: Boolean = _
    def init(self: SyncManyObserver[T]) {
      done = false
    }
    init(this)
    def checkReady(self: SyncManyObserver[T]) {
      var i = 0
      while (i < buffers.length) {
        if (buffers(i).isEmpty) return
        i += 1
      }
      val batch = mutable.Buffer[T]()
      i = 0
      while (i < buffers.length) {
        batch += buffers(i).dequeue()
        i += 1
      }
      target.react(batch, null)
    }
    def react(value: T, hint: Any) {
      buffer.enqueue(value)
      checkReady(this)
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      if (!done) {
        done = true
        subscription.unsubscribe()
        target.unreact()
      }
    }
  }

  private[reactors] class ScanPast[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val self: Events[T],
    val z: S,
    val op: (S, T) => S
  ) extends Events[S] {
    def onReaction(observer: Observer[S]): Subscription =
      self.onReaction(new ScanPastObserver(observer, z, op))
  }

  private[reactors] class ScanPastObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val target: Observer[S],
    private var cached: S,
    val op: (S, T) => S
  ) extends Observer[T] {
    def apply() = cached
    def react(value: T, hint: Any) {
      try {
        cached = op(cached, value)
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
      target.react(cached, hint)
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      target.unreact()
    }
  }

  private[reactors] class ReducePast[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val self: Events[T],
    val z: S,
    val op: (S, T) => S
  ) extends Events[S] {
    def onReaction(observer: Observer[S]): Subscription =
      self.onReaction(new ReducePastObserver(observer, z, op))
  }

  private[reactors] class ReducePastObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val target: Observer[S],
    private var cached: S,
    val op: (S, T) => S
  ) extends Observer[T] {
    def apply() = cached
    def react(value: T, hint: Any) {
      try {
        cached = op(cached, value)
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      target.react(cached, null)
      target.unreact()
    }
  }

  private[reactors] class ToSignal[@spec(Int, Long, Double) T](
    val self: Events[T],
    private var full: Boolean,
    private var cached: T
  ) extends Signal[T] with Observer[T] with Subscription.Proxy {
    private var pushSource: PushSource[T] = _
    private var rawSubscription: Subscription = _
    private var done = false
    def subscription = rawSubscription
    def init(dummy: T) {
      pushSource = new PushSource[T]
      rawSubscription = self.onReaction(this)
    }
    init(cached)
    override def onReaction(obs: Observer[T]): Subscription = {
      if (done) {
        obs.unreact()
        Subscription.empty
      } else {
        if (full) obs.react(cached, null)
        pushSource.onReaction(obs)
      }
    }
    def apply(): T = {
      if (full) cached
      else throw new NoSuchElementException
    }
    def isEmpty = !full
    def react(x: T, hint: Any) {
      cached = x
      if (!full) full = true
      pushSource.reactAll(x, hint)
    }
    def except(t: Throwable) = pushSource.exceptAll(t)
    def unreact() = {
      done = true
      pushSource.unreactAll()
    }
  }

  private[reactors] class ToColdSignal[@spec(Int, Long, Double) T](
    val self: Events[T],
    var cached: T
  ) extends Signal[T] {
    var selfSubscription: Subscription = null
    var subscriptions: Subscription.Collection = _
    var pushSource: PushSource[T] = _
    def init(dummy: Events[T]) {
      pushSource = new PushSource[T]
      subscriptions = new Subscription.Collection
    }
    init(self)
    def apply() = cached
    def isEmpty = false
    def unsubscribe() {}
    override def onReaction(target: Observer[T]): Subscription = {
      val obs = new ToColdSignalObserver(target, this)
      val sub = pushSource.onReaction(obs)
      if (!obs.done) {
        if (subscriptions.isEmpty) {
          selfSubscription = self.onReaction(new ToColdSelfObserver(this))
        }
        val savedsub = subscriptions.addAndGet(sub)
        savedsub.andThen(checkUnsubscribe())
      } else Subscription.empty
    }
    def checkUnsubscribe() {
      if (subscriptions.isEmpty && selfSubscription != null) {
        selfSubscription.unsubscribe()
        selfSubscription = null
      }
    }
  }

  private[reactors] class ToColdSelfObserver[@spec(Int, Long, Double) T](
    val signal: ToColdSignal[T]
  ) extends Observer[T] {
    def react(x: T, hint: Any) = signal.pushSource.reactAll(x, hint)
    def except(t: Throwable) = signal.pushSource.exceptAll(t)
    def unreact() = signal.pushSource.unreactAll()
  }

  private[reactors] class ToColdSignalObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val signal: ToColdSignal[T]
  ) extends Observer[T] {
    var done = false
    def react(x: T, hint: Any) = {
      signal.cached = x
      target.react(x, hint)
    }
    def except(t: Throwable) = target.except(t)
    def unreact() {
      done = true
      signal.checkUnsubscribe()
      target.unreact()
    }
  }

  private[reactors] class ToRCell[@spec(Int, Long, Double) T](
    val cell: RCell[T]
  ) extends Observer[T] {
    def react(value: T, hint: Any) = cell := value
    def except(t: Throwable) = cell.except(t)
    def unreact() {}
  }

  private[reactors] class ToIVar[@spec(Int, Long, Double) T](
    val ivar: IVar[T]
  ) extends Observer[T] {
    var subscription: Subscription = _
    def react(value: T, hint: Any) = if (ivar.isUnassigned) {
      try ivar := value
      finally subscription.unsubscribe()
    }
    def except(t: Throwable) = if (ivar.isUnassigned) {
      try ivar.except(t)
      finally subscription.unsubscribe()
    }
    def unreact() = if (ivar.isUnassigned) {
      try ivar.unreact()
      finally subscription.unsubscribe()
    }
  }

  private[reactors] class Count[@spec(Int, Long, Double) T](val self: Events[T])
  extends Events[Int] {
    private def newCountObserver(observer: Observer[Int]): Observer[T] =
      new CountObserver[T](observer)
    def onReaction(observer: Observer[Int]): Subscription =
      self.onReaction(newCountObserver(observer))
  }

  private[reactors] class CountObserver[@spec(Int, Long, Double) T](
    val target: Observer[Int]
  ) extends Observer[T] {
    private var cnt: Int = _
    def init(dummy: Observer[T]) {
      cnt = 0
    }
    init(this)
    def apply() = cnt
    def react(value: T, hint: Any) {
      cnt += 1
      target.react(cnt, hint)
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      target.unreact()
    }
  }

  private[reactors] class Changed[@spec(Int, Long, Double) T](
    val self: Events[T],
    val initial: T
  ) extends Events[T] {
    private def newChangedObserver(observer: Observer[T]): Observer[T] =
      new ChangedObserver[T](observer, initial)
    def onReaction(observer: Observer[T]): Subscription =
      self.onReaction(newChangedObserver(observer))
  }

  private[reactors] class ChangedObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    var last: T
  ) extends Observer[T] {
    def react(value: T, hint: Any) {
      if (value != last) {
        last = value
        target.react(value, hint)
      }
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      target.unreact()
    }
  }

  private[reactors] class After[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val self: Events[T],
    val that: Events[S]
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription = {
      val afterObserver = new AfterObserver(observer, that)
      val afterThatObserver = new AfterThatObserver[T, S](afterObserver)
      val sub = self.onReaction(afterObserver)
      val subThat = that.onReaction(afterThatObserver)
      afterThatObserver.subscription = subThat
      new Subscription.Composite(sub, subThat)
    }
  }

  private[reactors] class AfterObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val target: Observer[T],
    val that: Events[S]
  ) extends Observer[T] {
    private[reactors] var rawStarted = false
    private[reactors] var rawLive = true
    def started = rawStarted
    def started_=(v: Boolean) = rawStarted = v
    def live = rawLive
    def live_=(v: Boolean) = rawLive = v
    def tryUnreact() = if (live) {
      live = false
      target.unreact()
    }
    def react(value: T, hint: Any) {
      if (started) target.react(value, hint)
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() = tryUnreact()
  }

  private[reactors] class AfterThatObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](val afterObserver: AfterObserver[T, S]) extends Observer[S] {
    var subscription = Subscription.empty
    def react(value: S, hint: Any) {
      if (!afterObserver.started) {
        afterObserver.started = true
        subscription.unsubscribe()
      }
    }
    def except(t: Throwable) {
      if (!afterObserver.started) afterObserver.target.except(t)
    }
    def unreact() = if (!afterObserver.started) afterObserver.tryUnreact()
  }

  private[reactors] class Until[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val self: Events[T],
    val that: Events[S]
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription = {
      val untilObserver = new UntilObserver(observer, that)
      val untilThatObserver = new UntilThatObserver[T, S](untilObserver)
      val sub = new Subscription.Composite(
        self.onReaction(untilObserver),
        that.onReaction(untilThatObserver)
      )
      untilObserver.subscription = sub
      sub
    }
  }

  private[reactors] class UntilObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val target: Observer[T],
    val that: Events[S]
  ) extends Observer[T] {
    private[reactors] var rawLive = true
    var subscription = Subscription.empty
    def live = rawLive
    def live_=(v: Boolean) = rawLive = v
    def tryUnreact() = if (live) {
      live = false
      subscription.unsubscribe()
      target.unreact()
    }
    def react(value: T, hint: Any) {
      if (live) target.react(value, hint)
    }
    def except(t: Throwable) {
      if (live) target.except(t)
    }
    def unreact() = tryUnreact()
  }

  private[reactors] class UntilThatObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](val untilObserver: UntilObserver[T, S]) extends Observer[S] {
    def react(value: S, hint: Any) = untilObserver.tryUnreact()
    def except(t: Throwable) {
      if (untilObserver.live) untilObserver.target.except(t)
    }
    def unreact() = {}
  }

  private[reactors] class Defer[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val self: Events[T],
    val that: Events[S]
  )(implicit a: Arrayable[T]) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription = {
      val delayObserver = new DeferObserver[T, S](observer, false, false, false)
      val delayThatObserver = new DeferThatObserver(delayObserver)
      delayObserver.selfSubscription = self.onReaction(delayObserver)
      delayObserver.thatSubscription = that.onReaction(delayThatObserver)
      new Subscription.Composite(
        delayObserver.selfSubscription,
        delayObserver.thatSubscription
      )
    }
  }

  private[reactors] class DeferObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val target: Observer[T],
    var canForward: Boolean,
    var mustTerminate: Boolean,
    var hasTerminated: Boolean
  )(implicit val a: Arrayable[T]) extends Observer[T] {
    private[reactors] var buffer: UnrolledRing[T] = _
    private[reactors] var selfSubscription: Subscription = _
    private[reactors] var thatSubscription: Subscription = _
    def init(self: DeferObserver[T, S]): Unit = {
      buffer = new UnrolledRing[T]
    }
    init(this)
    def react(x: T, hint: Any): Unit = {
      if (canForward) target.react(x, null)
      else buffer.enqueue(x)
    }
    def except(t: Throwable): Unit = {
      target.except(t)
    }
    def unreact(): Unit = {
      mustTerminate = true
      if (canForward && !hasTerminated) {
        hasTerminated = true
        thatSubscription.unsubscribe()
        target.unreact()
      }
    }
  }

  private[reactors] class DeferThatObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val delayObserver: DeferObserver[T, S]
  ) extends Observer[S] {
    def react(x: S, hint: Any): Unit = {
      delayObserver.thatSubscription.unsubscribe()
      delayObserver.canForward = true
      while (delayObserver.buffer.nonEmpty) {
        val x = delayObserver.buffer.dequeue()
        delayObserver.target.react(x, null)
      }
      if (delayObserver.mustTerminate && !delayObserver.hasTerminated) {
        delayObserver.target.unreact()
      }
    }
    def except(t: Throwable): Unit = {
      delayObserver.target.except(t)
    }
    def unreact(): Unit = {}
  }

  private[reactors] class Once[@spec(Int, Long, Double) T](val self: Events[T])
  extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription = {
      val obs = new OnceObserver(observer)
      val sub = self.onReaction(obs)
      obs.subscription = sub
      sub
    }
  }

  private[reactors] class OnceObserver[@spec(Int, Long, Double) T](
    val target: Observer[T]
  ) extends Observer[T] {
    private var seen: Boolean = _
    var subscription = Subscription.empty
    def init(dummy: Observer[T]) {
      seen = false
    }
    init(this)
    def react(value: T, hint: Any) = if (!seen) {
      seen = true
      subscription.unsubscribe()
      target.react(value, hint)
      target.unreact()
    }
    def except(t: Throwable) = if (!seen) {
      target.except(t)
    }
    def unreact() = if (!seen) {
      target.unreact()
    }
  }

  private[reactors] class Last[@spec(Int, Long, Double) T](val self: Events[T])
  extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription = {
      val obs = new LastObserver(observer)
      val sub = self.onReaction(obs)
      obs.subscription = sub
      sub
    }
  }

  private[reactors] class LastObserver[@spec(Int, Long, Double) T](
    val target: Observer[T]
  ) extends Observer[T] {
    private var last: T =_
    private var seen: Boolean = _
    var subscription = Subscription.empty
    def init(dummy: Observer[T]) {
      seen = false
    }
    init(this)
    def react(value: T, hint: Any) = {
      seen = true
      last = value
    }
    def except(t: Throwable) = if (!seen) {
      target.except(t)
    }
    def unreact() = {
      if (seen) target.react(last, null)
      target.unreact()
    }
  }

  private[reactors] class Filter[@spec(Int, Long, Double) T](
    val self: Events[T],
    val p: T => Boolean
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription =
      self.onReaction(new FilterObserver(observer, p))
  }

  private[reactors] class FilterObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val p: T => Boolean
  ) extends Observer[T] {
    def react(value: T, hint: Any) = {
      val ok = try p(value) catch {
        case NonLethal(t) =>
          target.except(t)
          false
      }
      if (ok) target.react(value, hint)
    }
    def except(t: Throwable) = {
      target.except(t)
    }
    def unreact() = {
      target.unreact()
    }
  }

  private[reactors] class Collect[T, S <: AnyRef](
    val self: Events[T],
    val pf: PartialFunction[T, S]
  ) extends Events[S] {
    def onReaction(observer: Observer[S]): Subscription =
      self.onReaction(new CollectObserver(observer, pf))
  }

  private[reactors] class CollectObserver[T, S <: AnyRef](
    val target: Observer[S],
    val pf: PartialFunction[T, S]
  ) extends Observer[T] {
    def react(value: T, hint: Any) = {
      val ok = try pf.isDefinedAt(value) catch {
        case NonLethal(t) =>
          target.except(t)
          false
      }
      if (ok) target.react(pf(value), hint)
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      target.unreact()
    }
  }

  private[reactors] class Map[
    @spec(Int, Long, Double) T,
    @spec(Boolean, Int, Long, Double) S
  ](
    val self: Events[T],
    val f: T => S
  ) extends Events[S] {
    def onReaction(observer: Observer[S]): Subscription =
      self.onReaction(new MapObserver(observer, f))
  }

  private[reactors] class MapObserver[
    @spec(Int, Long, Double) T,
    @spec(Boolean, Int, Long, Double) S
  ](
    val target: Observer[S],
    val f: T => S
  ) extends Observer[T] {
    def react(value: T, hint: Any) {
      val x = try {
        f(value)
      } catch {
        case NonLethal(t) =>
          target.except(t)
          return
      }
      target.react(x, hint)
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      target.unreact()
    }
  }

  private[reactors] class GroupBy[@spec(Int, Long, Double) T, K](
    val self: Events[T],
    val f: T => K
  ) extends Events[(K, Events[T])] {
    def onReaction(observer: Observer[(K, Events[T])]): Subscription =
      self.onReaction(new GroupByObserver(observer, f))
  }

  private[reactors] class GroupByObserver[@spec(Int, Long, Double) T, K](
    val target: Observer[(K, Events[T])],
    val f: T => K
  ) extends Observer[T] {
    val groups = mutable.Map[K, Events.Emitter[T]]()
    def react(value: T, hint: Any) {
      val k = try {
        f(value)
      } catch {
        case NonLethal(t) =>
          target.except(t)
          return
      }
      if (!groups.contains(k)) {
        val events = new Events.Emitter[T]
        groups(k) = events
        target.react((k, events), hint)
      }
      groups(k).react(value, hint)
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      target.unreact()
      for ((k, events) <- groups) events.unreact()
    }
  }

  private[reactors] class Sliding[@spec(Int, Long, Double) T](
    val self: Events[T],
    val sz: Int,
    val s: Spec[T]
  ) extends Events[Conc.Queue[T]] {
    def onReaction(observer: Observer[Conc.Queue[T]]) =
      self.onReaction(new SlidingObserver(observer, sz, s))
  }

  private[reactors] class SlidingObserver[@spec(Int, Long, Double) T](
    val target: Observer[Conc.Queue[T]],
    val sz: Int,
    val s: Spec[T]
  ) extends Observer[T] {
    private var queue = new Conc.Queue[T]()
    def react(value: T, hint: Any) {
      queue = queue.enqueue(value)
      if (queue.size > sz) queue = queue.dequeue()
      target.react(queue, hint)
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      target.unreact()
    }
  }

  private[reactors] class Batch[@spec(Int, Long, Double) T](
    val self: Events[T],
    val sz: Int
  ) extends Events[Seq[T]] {
    def onReaction(observer: Observer[Seq[T]]): Subscription =
      self.onReaction(new BatchObserver(observer, sz))
  }

  private[reactors] class BatchObserver[@spec(Int, Long, Double) T](
    val target: Observer[Seq[T]],
    val sz: Int
  ) extends Observer[T] {
    var currentBatch = mutable.ArrayBuffer[T]()
    def react(value: T, hint: Any) {
      currentBatch += value
      if (currentBatch.size == sz) {
        target.react(currentBatch, null)
        currentBatch = mutable.ArrayBuffer[T]()
      }
    }
    def except(t: Throwable) {
      target.except(t)
    }
    def unreact() {
      if (currentBatch.size > 0) {
        target.react(currentBatch, null)
        currentBatch = mutable.ArrayBuffer[T]()
      }
      target.unreact()
    }
  }

  private[reactors] class TakeWhile[@spec(Int, Long, Double) T](
    val self: Events[T],
    val p: T => Boolean
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription = {
      val obs = new TakeWhileObserver(observer, p)
      val sub = self.onReaction(obs)
      obs.subscription = sub
      sub
    }
  }

  private[reactors] class TakeWhileObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val p: T => Boolean
  ) extends Observer[T] {
    private var closed: Boolean = _
    var subscription = Subscription.empty
    def init(dummy: Observer[T]) {
      closed = false
    }
    init(this)
    def react(value: T, hint: Any) = if (!closed) {
      if (p(value)) target.react(value, hint)
      else {
        closed = true
        subscription.unsubscribe()
        target.unreact()
      }
    }
    def except(t: Throwable) = if (!closed) {
      target.except(t)
    }
    def unreact() = if (!closed) {
      target.unreact()
    }
  }

  private[reactors] class DropAfter[@spec(Int, Long, Double) T](
    val self: Events[T],
    val p: T => Boolean
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription = {
      val obs = new DropAfterObserver(observer, p)
      val sub = self.onReaction(obs)
      obs.subscription = sub
      sub
    }
  }

  private[reactors] class DropAfterObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val p: T => Boolean
  ) extends Observer[T] {
    private var closed: Boolean = _
    var subscription = Subscription.empty
    def init(dummy: Observer[T]) {
      closed = false
    }
    init(this)
    def react(value: T, hint: Any) = if (!closed) {
      if (!p(value)) target.react(value, hint)
      else {
        closed = true
        target.react(value, hint)
        subscription.unsubscribe()
        target.unreact()
      }
    }
    def except(t: Throwable) = if (!closed) {
      target.except(t)
    }
    def unreact() = if (!closed) {
      target.unreact()
    }
  }

  private[reactors] class DropWhile[@spec(Int, Long, Double) T](
    val self: Events[T],
    val p: T => Boolean
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription =
      self.onReaction(new DropWhileObserver(observer, p))
  }

  private[reactors] class DropWhileObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val p: T => Boolean
  ) extends Observer[T] {
    private var started: Boolean = _
    def init(dummy: Observer[T]) {
      started = false
    }
    init(this)
    def react(value: T, hint: Any) = {
      if (!started && !p(value)) started = true
      if (started) target.react(value, hint)
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = target.unreact()
  }

  private[reactors] class Take[@spec(Int, Long, Double) T](
    val self: Events[T],
    val n: Int
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription =
      self.onReaction(new TakeObserver(observer, n))
  }

  private[reactors] class TakeObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    var n: Int
  ) extends Observer[T] {
    def react(value: T, hint: Any) = {
      if (n > 0) {
        n -= 1
        target.react(value, hint)
      }
      if (n == 0) {
        n = -1
        target.unreact()
      }
    }
    def except(t: Throwable) = if (n > 0) target.except(t)
    def unreact() = if (n > 0) {
      n = -1
      target.unreact()
    }
  }

  private[reactors] class Drop[@spec(Int, Long, Double) T](
    val self: Events[T],
    val n: Int
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription =
      self.onReaction(new DropObserver(observer, n))
  }

  private[reactors] class DropObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    var n: Int
  ) extends Observer[T] {
    def react(value: T, hint: Any) = {
      if (n <= 0) target.react(value, hint)
      else n -= 1
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = target.unreact()
  }

  private[reactors] class Mux[T, @spec(Int, Long, Double) S: Spec](
    val self: Events[T],
    val evid: T <:< Events[S]
  ) extends Events[S] {
    def onReaction(observer: Observer[S]): Subscription =
      self.onReaction(new MuxObserver(observer, evid))
  }

  private[reactors] class MuxObserver[T, @spec(Int, Long, Double) S: Spec](
    val target: Observer[S],
    val evidence: T <:< Events[S]
  ) extends Observer[T] {
    private[reactors] var currentSubscription: Subscription = _
    private[reactors] var terminated = false
    def init(e: T <:< Events[S]) {
      currentSubscription = Subscription.empty
    }
    init(evidence)
    def checkUnreact() =
      if (terminated && currentSubscription == Subscription.empty) target.unreact()
    def newMuxNestedObserver: Observer[S] = new MuxNestedObserver(target, this)
    def react(value: T, hint: Any): Unit = if (!terminated) {
      val nextEvents = try {
        evidence(value)
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
      currentSubscription.unsubscribe()
      currentSubscription = nextEvents.onReaction(newMuxNestedObserver)
    }
    def except(t: Throwable) = if (!terminated) {
      target.except(t)
    }
    def unreact() = if (!terminated) {
      terminated = true
      checkUnreact()
    }
  }

  private[reactors] class MuxNestedObserver[T, @spec(Int, Long, Double) S: Spec](
    val target: Observer[S],
    val muxObserver: MuxObserver[T, S]
  ) extends Observer[S] {
    def react(value: S, hint: Any) = {
      target.react(value, hint)
    }
    def except(t: Throwable) = target.except(t)
    def unreact() {
      muxObserver.currentSubscription = Subscription.empty
      muxObserver.checkUnreact()
    }
  }

  private[reactors] class Unreacted[@spec(Int, Long, Double) T](
    val self: Events[T]
  ) extends Events[Unit] {
    def newUnreactedObserver(obs: Observer[Unit]): UnreactedObserver[T] =
      new UnreactedObserver[T](obs)
    def onReaction(observer: Observer[Unit]): Subscription = {
      val obs = newUnreactedObserver(observer)
      val sub = self.onReaction(obs)
      obs.subscription = sub
      sub
    }
  }

  private[reactors] class UnreactedObserver[@spec(Int, Long, Double) T](
    val target: Observer[Unit]
  ) extends Observer[T] {
    var subscription = Subscription.empty
    def react(value: T, hint: Any) = {}
    def except(t: Throwable) = target.except(t)
    def unreact() {
      target.react((), null)
      target.unreact()
      subscription.unsubscribe()
    }
  }

  private[reactors] class Union[@spec(Int, Long, Double) T](
    val self: Events[T],
    val that: Events[T]
  ) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription = {
      val count = new IntRef(0)
      new Subscription.Composite(
        self.onReaction(new UnionObserver(observer, count)),
        that.onReaction(new UnionObserver(observer, count)))
    }
  }

  private[reactors] class UnionObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val count: IntRef
  ) extends Observer[T] {
    def react(value: T, hint: Any) = target.react(value, hint)
    def except(t: Throwable) = target.except(t)
    def unreact() = {
      count.elem += 1
      if (count.elem == 2) target.unreact()
    }
  }

  private[reactors] class Concat[@spec(Int, Long, Double) T](
    val self: Events[T],
    val that: Events[T]
  )(implicit val a: Arrayable[T]) extends Events[T] {
    def onReaction(obs: Observer[T]): Subscription = {
      val thatObserver = new ConcatThatObserver(obs, new UnrolledBuffer[T])
      val thisObserver = new ConcatObserver(obs, thatObserver)
      new Subscription.Composite(
        self.onReaction(thisObserver),
        that.onReaction(thatObserver))
    }
  }

  private[reactors] class ConcatObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val thatObserver: ConcatThatObserver[T]
  ) extends Observer[T] {
    def react(value: T, hint: Any) = target.react(value, hint)
    def except(t: Throwable) = target.except(t)
    def unload(dummy: Observer[T]) {
      while (thatObserver.buffer.nonEmpty) {
        target.react(thatObserver.buffer.dequeue(), null)
      }
    }
    def unreact() = {
      thatObserver.selfObserverDone = true
      unload(this)
      thatObserver.tryUnreact()
    }
  }

  private[reactors] class ConcatThatObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val buffer: UnrolledBuffer[T]
  ) extends Observer[T] {
    private[reactors] var selfObserverDone = false
    private[reactors] var thatObserverDone = false
    def react(value: T, hint: Any) = {
      if (selfObserverDone) target.react(value, hint)
      else buffer.enqueue(value)
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = {
      thatObserverDone = true
      tryUnreact()
    }
    def tryUnreact() = if (selfObserverDone && thatObserverDone) {
      target.unreact()
    }
  }

  private[reactors] class Sync[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S,
    @spec(Int, Long, Double) R
  ](
    val self: Events[T],
    val that: Events[S],
    val f: (T, S) => R
  )(
    implicit val at: Arrayable[T],
    implicit val as: Arrayable[S]
  ) extends Events[R] {
    def newSyncThisObserver(state: SyncState[T, S, R], obs: Observer[R]) =
      new SyncThisObserver(obs, state, f)
    def newSyncThatObserver(state: SyncState[T, S, R], obs: Observer[R]) =
      new SyncThatObserver(obs, state, f)
    def onReaction(obs: Observer[R]) = {
      val state = new SyncState[T, S, R](new UnrolledRing[T], new UnrolledRing[S])
      new Subscription.Composite(
        self.onReaction(newSyncThisObserver(state, obs)),
        that.onReaction(newSyncThatObserver(state, obs))
      )
    }
  }

  private[reactors] class SyncState[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S,
    @spec(Int, Long, Double) R
  ](val tbuffer: UnrolledRing[T], val sbuffer: UnrolledRing[S]) {
    var thisSub = Subscription.empty
    var thatSub = Subscription.empty
    var live = true
    def unreactBoth(target: Observer[R]) = if (live) {
      tbuffer.clear()
      sbuffer.clear()
      thisSub.unsubscribe()
      thatSub.unsubscribe()
      live = false
      target.unreact()
    }
  }

  private[reactors] class SyncThisObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S,
    @spec(Int, Long, Double) R
  ](
    val target: Observer[R], val state: SyncState[T, S, R], val f: (T, S) => R
  ) extends Observer[T] {
    def react(tvalue: T, hint: Any) {
      if (state.sbuffer.isEmpty) state.tbuffer.enqueue(tvalue)
      else {
        val svalue = state.sbuffer.dequeue()
        val event = try {
          f(tvalue, svalue)
        } catch {
          case t if isNonLethal(t) =>
            target.except(t)
            return
        }
        target.react(event, null)
      }
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = state.unreactBoth(target)
  }

  private[reactors] class SyncThatObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S,
    @spec(Int, Long, Double) R
  ](
    val target: Observer[R], val state: SyncState[T, S, R], f: (T, S) => R
  ) extends Observer[S] {
    def react(svalue: S, hint: Any) {
      if (state.tbuffer.isEmpty) state.sbuffer.enqueue(svalue)
      else {
        val tvalue = state.tbuffer.dequeue()
        val event = try {
          f(tvalue, svalue)
        } catch {
          case t if isNonLethal(t) =>
            target.except(t)
            return
        }
        target.react(event, null)
      }
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = state.unreactBoth(target)
  }

  private[reactors] class Reverse[@spec(Int, Long, Double) T](
    val self: Events[T]
  )(implicit val a: Arrayable[T]) extends Events[T] {
    def onReaction(observer: Observer[T]): Subscription = {
      val reverseObserver = new ReverseObserver(observer)
      self.onReaction(reverseObserver)
    }
  }

  private[reactors] class ReverseObserver[@spec(Int, Long, Double) T](
    val target: Observer[T]
  )(implicit val a: Arrayable[T]) extends Observer[T] {
    var stack: Stack[T] = _
    var hintstack: Stack[Any] = _

    def init(implicit a: Arrayable[T]): Unit = {
      stack = new Stack[T]
      hintstack = new Stack[Any]
    }
    init(a)

    def react(value: T, hint: Any): Unit = {
      stack.push(value)
      hintstack.push(hint)
    }

    def except(t: Throwable): Unit = target.except(t)

    private def flush(a: Arrayable[T]): Unit = {
      while (stack.nonEmpty) {
        target.react(stack.pop(), hintstack.pop())
      }
    }

    def unreact(): Unit = {
      flush(a)
      target.unreact()
    }
  }

  private[reactors] class PostfixUnion[T, @spec(Int, Long, Double) S: Spec](
    val self: Events[T],
    val evid: T <:< Events[S]
  ) extends Events[S] {
    def onReaction(observer: Observer[S]): Subscription = {
      val postfixObserver = new PostfixUnionObserver(observer, evid)
      val sub = self.onReaction(postfixObserver)
      postfixObserver.outerSubscription.set(
        postfixObserver.allSubscriptions.addAndGet(sub))
      postfixObserver.allSubscriptions
    }
  }

  private[reactors] class PostfixUnionObserver[T, @spec(Int, Long, Double) S: Spec](
    val target: Observer[S],
    val evidence: T <:< Events[S]
  ) extends Observer[T] {
    private[reactors] var terminated: Boolean = _
    private[reactors] var outerSubscription: Subscription.Cell = _
    private[reactors] var allSubscriptions: Subscription.Collection = _
    def init(e: T <:< Events[S]) {
      terminated = false
      outerSubscription = new Subscription.Cell
      allSubscriptions = new Subscription.Collection
    }
    init(evidence)
    def checkUnreact() =
      if (allSubscriptions.isEmpty) target.unreact()
    def newPostfixUnionNestedObserver: PostfixUnionNestedObserver[T, S] =
      new PostfixUnionNestedObserver(target, this)
    def react(value: T, hint: Any): Unit = if (!terminated) {
      val moreEvents = try {
        evidence(value)
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
      val obs = newPostfixUnionNestedObserver
      val sub = allSubscriptions.addAndGet(moreEvents.onReaction(obs))
      obs.subscription.set(sub)
    }
    def except(t: Throwable) = if (!terminated) {
      target.except(t)
    }
    def unreact() = {
      terminated = true
      outerSubscription.unsubscribe()
      checkUnreact()
    }
  }

  private[reactors] class PostfixUnionNestedObserver[
    T, @spec(Int, Long, Double) S: Spec
  ](
    val target: Observer[S],
    val unionObserver: PostfixUnionObserver[T, S]
  ) extends Observer[S] {
    var subscription: Subscription.Cell = _
    def init(self: PostfixUnionNestedObserver[T, S]) {
      subscription = new Subscription.Cell
    }
    init(this)
    def react(value: S, hint: Any) = target.react(value, hint)
    def except(t: Throwable) = target.except(t)
    def unreact() {
      subscription.unsubscribe()
      unionObserver.checkUnreact()
    }
  }

  private[reactors] class PostfixConcat[T, @spec(Int, Long, Double) S: Spec](
    val self: Events[T],
    val evid: T <:< Events[S],
    val a: Arrayable[S]
  ) extends Events[S] {
    def onReaction(observer: Observer[S]): Subscription = {
      val postfixObserver = new PostfixConcatObserver(observer, evid, a)
      val sub = self.onReaction(postfixObserver)
      postfixObserver.subscription = postfixObserver.subscriptions.addAndGet(sub)
      postfixObserver.subscriptions
    }
  }

  private[reactors] class PostfixConcatObserver[T, @spec(Int, Long, Double) S: Spec](
    val target: Observer[S],
    val evidence: T <:< Events[S],
    val a: Arrayable[S]
  ) extends Observer[T] {
    private[reactors] var terminated: Boolean = _
    private[reactors] var subscription: Subscription = _
    private[reactors] var subscriptions: Subscription.Collection = _
    private[reactors] var queue: UnrolledRing[PostfixConcatNestedObserver[T, S]] = _
    def init(obs: Observer[S]) {
      terminated = false
      subscriptions = new Subscription.Collection
      queue = new UnrolledRing[PostfixConcatNestedObserver[T, S]]
    }
    init(target)
    def checkUnreact() =
      if (subscriptions.isEmpty) target.unreact()
    def newPostfixConcatNestedObserver: PostfixConcatNestedObserver[T, S] = {
      val obs = new PostfixConcatNestedObserver(
        target, this, new UnrolledBuffer[S]()(a))
      queue.enqueue(obs)
      obs
    }
    def react(value: T, hint: Any): Unit = if (!terminated) {
      val moreEvents = try {
        evidence(value)
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
      val obs = newPostfixConcatNestedObserver
      val sub = subscriptions.addAndGet(moreEvents.onReaction(obs))
      obs.subscription = sub
    }
    def except(t: Throwable) = if (!terminated) {
      target.except(t)
    }
    def unreact() = {
      terminated = true
      subscription.unsubscribe()
      checkUnreact()
    }
  }

  private[reactors] class PostfixConcatNestedObserver[
    T, @spec(Int, Long, Double) S: Spec
  ](
    val target: Observer[S],
    val concatObserver: PostfixConcatObserver[T, S],
    val buffer: UnrolledBuffer[S]
  ) extends Observer[S] {
    var subscription: Subscription = _
    var terminated: Boolean = false
    def react(value: S, hint: Any) = if (!terminated) {
      if (concatObserver.queue.head eq this) target.react(value, hint)
      else buffer.enqueue(value)
    }
    def except(t: Throwable) = if (!terminated) target.except(t)
    def unreact() = if (!terminated) {
      terminated = true
      subscription.unsubscribe()
      // remove all terminated observers from queue and flush their events
      while (concatObserver.queue.nonEmpty && concatObserver.queue.head.terminated) {
        val obs = concatObserver.queue.dequeue()
        while (obs.buffer.nonEmpty) target.react(obs.buffer.dequeue(), null)
      }
      // flush the events in the head
      while (concatObserver.queue.nonEmpty && concatObserver.queue.head.buffer.nonEmpty)
        target.react(concatObserver.queue.head.buffer.dequeue(), null)
      concatObserver.checkUnreact()
    }
  }

  private[reactors] class PostfixFirst[T, @spec(Int, Long, Double) S: Spec](
    val self: Events[T],
    val evidence: T <:< Events[S]
  ) extends Events[S] {
    def onReaction(observer: Observer[S]): Subscription = {
      val postfixObserver = new PostfixFirstObserver(observer, evidence)
      val sub = self.onReaction(postfixObserver)
      postfixObserver.topSub = sub
      sub
    }
  }

  private[reactors] class PostfixFirstObserver[T, @spec(Int, Long, Double) S: Spec](
    val target: Observer[S],
    val evidence: T <:< Events[S]
  ) extends Observer[T] {
    private[reactors] var first: Observer[S] = null
    private[reactors] var done = false
    private[reactors] var topSub: Subscription = Subscription.empty
    private[reactors] val nestedSubs = new Subscription.Collection
    def newNestedPostfixFirstObserver =
      new NestedPostfixFirstObserver(target, this)
    def react(x: T, hint: Any) {
      if (first != null) return
      val events = try {
        evidence(x)
      } catch {
        case NonLethal(t) =>
          except(t)
          return
      }
      val nestedObserver = newNestedPostfixFirstObserver
      val sub = try {
        events.onReaction(nestedObserver)
      } catch {
        case NonLethal(t) =>
          except(t)
          return
      }
      nestedObserver.subscription = nestedSubs.addAndGet(sub)
    }
    def except(t: Throwable) = target.except(t)
    def unreact() {
      if (!done) {
        done = true
        if (nestedSubs.isEmpty) target.unreact()
      }
    }
  }

  private[reactors] class NestedPostfixFirstObserver[
    T, @spec(Int, Long, Double) S: Spec
  ](
    val target: Observer[S],
    val postfixObserver: PostfixFirstObserver[T, S]
  ) extends Observer[S] {
    private[reactors] var subscription: Subscription = Subscription.empty
    def react(x: S, hint: Any) = {
      if (postfixObserver.first == null) {
        postfixObserver.topSub.unsubscribe()
        postfixObserver.nestedSubs.remove(subscription)
        postfixObserver.nestedSubs.unsubscribe()
        postfixObserver.first = this
      }
      if (postfixObserver.first eq this) target.react(x, hint)
    }
    def except(t: Throwable) = target.except(t)
    def unreact() {
      this.subscription.unsubscribe()
      if (postfixObserver.done) {
        if (postfixObserver.first eq null) {
          if (postfixObserver.nestedSubs.isEmpty) target.unreact()
        } else {
          if (postfixObserver.first eq this) target.unreact()
        }
      } else {
        if (postfixObserver.first eq this) target.unreact()
      }
    }
  }

  private[reactors] class Possibly[@spec(Int, Long, Double) T](
    val self: Events[T],
    val probability: Double
  ) extends Events[T] {
    def onReaction(obs: Observer[T]): Subscription =
      self.onReaction(new PossiblyObserver(obs, probability))
  }

  private[reactors] class PossiblyObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val probability: Double
  ) extends Observer[T] {
    private[reactors] val random = new Random
    def react(x: T, hint: Any) =
      if (random.nextDouble < probability) target.react(x, hint)
    def except(t: Throwable) = target.except(t)
    def unreact() = target.unreact()
  }

  private[reactors] class ZipHint[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val self: Events[T],
    val f: (T, Any) => S
  ) extends Events[S] {
    def onReaction(obs: Observer[S]): Subscription =
      self.onReaction(new ZipHintObserver(obs, f))
  }

  private[reactors] class ZipHintObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val target: Observer[S],
    val f: (T, Any) => S
  ) extends Observer[T] {
    def react(x: T, hint: Any): Unit = {
      val v = try {
        f(x, hint)
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
      target.react(v, null)
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = target.unreact()
  }

  private[reactors] class LiftTry[T](
    val self: Events[T]
  ) extends Events[Try[T]] {
    def onReaction(obs: Observer[Try[T]]): Subscription =
      self.onReaction(new LiftTryObserver(obs))
  }

  private[reactors] class LiftTryObserver[T](
    val target: Observer[Try[T]]
  ) extends Observer[T] {
    def react(x: T, hint: Any): Unit = {
      target.react(Success(x), null)
    }
    def except(t: Throwable) = target.react(Failure(t), null)
    def unreact() = target.unreact()
  }

  private[reactors] class UnliftTry[T, S](
    val self: Events[T],
    val evid: T <:< Try[S]
  ) extends Events[S] {
    def onReaction(obs: Observer[S]): Subscription =
      self.onReaction(new UnliftTryObserver(obs, evid))
  }

  private[reactors] class UnliftTryObserver[T, S](
    val target: Observer[S],
    val evid: T <:< Try[S]
  ) extends Observer[T] {
    def react(x: T, hint: Any): Unit = {
      val t = try {
        evid(x)
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
      t match {
        case Success(x) => target.react(x, hint)
        case Failure(t) => target.except(t)
      }
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = target.unreact()
  }

  private[reactors] class Incremental[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val self: Events[T],
    val state: () => (Subscription, Observer[S] => Unit)
  ) extends Events[S] {
    def onReaction(obs: Observer[S]): Subscription = {
      val (sub, sampler) = state()
      new Subscription.Composite(
        sub,
        self.onReaction(new IncrementalObserver(self, sub, obs, sampler))
      )
    }
  }

  private[reactors] class IncrementalObserver[
    @spec(Int, Long, Double) T,
    @spec(Int, Long, Double) S
  ](
    val self: Events[T],
    val subscription: Subscription,
    val target: Observer[S],
    val sampler: Observer[S] => Unit
  ) extends Observer[T] {
    def react(x: T, hint: Any): Unit = {
      try {
        sampler(target)
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = {
      subscription.unsubscribe()
      target.unreact()
    }
  }
  
  private[reactors] class Each[@spec(Int, Long, Double) T](
    val self: Events[T],
    val count: Int
  ) extends Events[T]{
    def onReaction(obs: Observer[T]): Subscription = {
      self.onReaction(new EachObserver[T](obs, count))
    }
  }

  private[reactors] class EachObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val count: Int
  ) extends Observer[T]{
    private var c = 0
    def init(self: EachObserver[T]): Unit = {
      if (count < 1) throw new IllegalArgumentException(
        s"The parameter `count` should be greater than 0, got $count")
    }
    init(this)
    def react(x: T, hint: Any): Unit = {
      c += 1
      if (c == count) {
        target.react(x, hint)
        c = 0
      }
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = target.unreact()
  }

  private[reactors] class Repeat[@spec(Int, Long, Double) T](
    val self: Events[T],
    val count: Int,
    val copy: T => T
  ) extends Events[T]{
    def onReaction(obs: Observer[T]): Subscription = {
      self.onReaction(new RepeatObserver[T](obs, count, copy))
    }
  }

  private[reactors] class RepeatObserver[@spec(Int, Long, Double) T](
    val target: Observer[T],
    val count: Int,
    val copy: T => T
  ) extends Observer[T]{
    def init(self: EachObserver[T]): Unit = {
      if (count < 1) throw new IllegalArgumentException(
        s"The parameter `count` should be greater than 0, got $count")
    }
    def react(x: T, hint: Any): Unit = {
      var c = 0
      while (c != count) {
        if (c == 0) target.react(x, hint)
        else target.react(copy(x), hint)
        c += 1
      }
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = target.unreact()
  }

  private[reactors] class PartitionObserver[@spec(Int, Long, Double) T](
    val trueTarget: Events.Emitter[T],
    val falseTarget: Events.Emitter[T],
    val p: T => Boolean
  ) extends Observer[T]{
    def react(x: T, hint: Any): Unit = {
      val isTrue = try {
        p(x)
      } catch {
        case t if isNonLethal(t) =>
          trueTarget.except(t)
          falseTarget.except(t)
          return
      }
      if (isTrue) trueTarget.react(x, hint)
      else falseTarget.react(x, hint)
    }
    def except(t: Throwable) = {
      trueTarget.except(t)
      falseTarget.except(t)
    }
    def unreact() = {
      trueTarget.unreact()
      falseTarget.unreact()
    }
  }

  private[reactors] class CollectHint[@spec(Int, Long, Double) T, W](
    val self: Events[T],
    val pf: PartialFunction[Any, W]
  ) extends Events[T] {
    def onReaction(obs: Observer[T]): Subscription =
      self.onReaction(new CollectHintObserver(obs, pf))
  }

  private[reactors] class CollectHintObserver[@spec(Int, Long, Double) T, W](
    val target: Observer[T],
    val pf: PartialFunction[Any, W]
  ) extends Observer[T] {
    def react(x: T, hint: Any): Unit = {
      try {
        if (!pf.isDefinedAt(hint)) return
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
      val v = try {
        pf(hint)
      } catch {
        case t if isNonLethal(t) =>
          target.except(t)
          return
      }
      target.react(x, v)
    }
    def except(t: Throwable) = target.except(t)
    def unreact() = target.unreact()
  }

}
