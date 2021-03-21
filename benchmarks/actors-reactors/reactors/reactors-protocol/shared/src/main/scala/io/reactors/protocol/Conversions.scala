package io.reactors
package protocol



import scala.concurrent._
import scala.concurrent.ExecutionContext.Implicits.global
import scala.util.Try



/** Utilities that convert values of different types to events streams.
 */
trait Conversions {
  /** Methods that convert collections to event streams.
   *
   *  Since standard collections are not specialized, boxing is potentially possible.
   */
  implicit class TraversableOps[T](val xs: Traversable[T]) {
    /** Converts a collection to an event stream.
     */
    def toEvents: Events[T] = new Conversions.ToEvents(xs)
  }

  implicit class FutureOps[T](val f: Future[T]) {
    /** Converts a future to an event stream.
     */
    def toIVar: IVar[T] = {
      val input = Reactor.self.system.channels.daemon.open[Try[T]]
      val ivar = input.events.unliftTry.toIVar
      input.events.on(input.seal())
      f onComplete {
        case t => input.channel ! t
      }
      ivar
    }
  }
}


object Conversions {
  private[protocol] class ToEvents[T](val xs: Traversable[T]) extends Events[T] {
    def onReaction(obs: Observer[T]): Subscription = {
      try {
        for (x <- xs) obs.react(x, null)
      } catch {
        case NonLethal(t) => obs.except(t)
      } finally {
        obs.unreact()
      }
      Subscription.empty
    }
  }
}
