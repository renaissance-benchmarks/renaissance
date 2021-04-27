package io.reactors
package protocol



import io.reactors.common.UnrolledRing
import scala.concurrent.duration._
import scala.util._



/** General communication patterns.
 *
 *  Allows specifying communication patterns in a generic way.
 *
 *  As an example, one can declaratively retry server requests until a timeout,
 *  by sending a throttled sequence of requests until a timeout, and taking the first
 *  reply that comes:
 *
 *  {{{
 *  Seq(1, 2, 4).toEvents.throttle(x => x.seconds).map(_ => server ? "req")
 *    .first.until(timeout(3.seconds))
 *  }}}
 */
trait Patterns {
  implicit class DurationEventOps[T](val events: Events[T]) {
    /** Delays each event by `Duration` returned by `f`.
     *
     *  Instead of being emitted immediately, events are asynchronously delayed and
     *  emitted one after the other, separated by at least time intervals specified by
     *  the function `f`.
     *
     *  Assuming that `f == (x: Int) => x.seconds`:
     *
     *  {{{
     *  this         ---1-2-3-------------------2------------->
     *  throttle(f)  ---1--------2----------3------------2---->
     *  time             <--2s--> <---3s--->     <--2s-->
     *  }}}
     *
     *  Note that exceptions on the current stream `events` result in unreacting the
     *  resulting event stream.
     *
     *  @param f         function that converts each event into a delay
     *  @return          an event stream with the throttled events
     */
    def throttle(f: T => Duration)(implicit a: Arrayable[T]): Events[T] =
      new Patterns.Throttle(events, f)
  }

  /** Retry the specified request a fixed number of times.
   *
   *  @param numTimes       the number of times to retry the request
   *  @param delay          the delay between each request
   *  @param req            the code that creates the request and a stream of replies
   *  @return               the stream of replies that was first to emit an event
   */
  def retry[T](numTimes: Int, delay: Duration)(req: =>Events[T]): Events[T] = {
    retry(Backoff.regular(numTimes, delay))(req)
  }

  /** Retry the specified request with a backoff scheme.
   *
   *  After a stream from one of the requests starts emitting events, all the other
   *  requests are unsubscribed from, and not further retrying takes place.
   *
   *  To create different backoff schemes, see the `Backoff` object.
   *
   *  @param backoffScheme  the duration of subsequent delays between requests
   *  @param req            the code that creates the request and a stream of replies
   *  @return               the stream of replies that was first to emit an event
   */
  def retry[T](backoffScheme: Seq[Duration])(req: =>Events[T]): Events[T] = {
    backoffScheme.toEvents.throttle(x => x).map(_ => req).first
  }

  /** Utility methods for frequently used delay sequences.
   */
  object Backoff {
    def regular(n: Int, delay: Duration): Seq[Duration] =
      (0 until n).map(_ => delay)
    def linear(n: Int, base: Duration, offset: Duration = 0.seconds): Seq[Duration] =
      (1 to n).map(_ * base + offset)
    def exp(n: Int, base: Duration, factor: Double = 2.0): Seq[Duration] =
      (0 until n).map(i => math.pow(factor, i) * base)
    def randexp(n: Int, base: Duration, factor: Double = 2.0): Seq[Duration] =
      (0 until n).map(i => {
        val min = math.pow(factor, i)
        val max = math.pow(factor, i + 1)
        val offset = min + (max - min) * Math.random()
        offset * base
      })
  }
}


object Patterns {
  private[protocol] class Throttle[T](val events: Events[T], val f: T => Duration)(
    implicit val a: Arrayable[T]
  ) extends Events[T] {
    def onReaction(obs: Observer[T]) =
      events.onReaction(new ThrottleObserver(obs, f))
  }

  private[protocol] class ThrottleObserver[T](
    val target: Observer[T], val f: T => Duration
  )(implicit val a: Arrayable[T]) extends Observer[T] {
    var done = false
    var queue = new UnrolledRing[T]
    def react(x: T, hint: Any) {
      def emitNext() {
        val x = queue.head
        val duration = try {
          f(x)
        } catch {
          case NonLethal(t) =>
            except(t)
            return
        }
        target.react(x, null)
        Reactor.self.system.clock.timeout(duration) on {
          queue.dequeue()
          if (queue.nonEmpty) emitNext()
        }
      }

      if (queue.isEmpty) {
        queue.enqueue(x)
        emitNext()
      } else {
        queue.enqueue(x)
      }
    }
    def except(t: Throwable) = {
      target.except(t)
      unreact()
    }
    def unreact() {
      done = true
      target.unreact()
    }
  }
}
