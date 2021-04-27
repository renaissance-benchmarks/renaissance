package io



import scala.annotation.implicitNotFound
import scala.util.control.NoStackTrace



package object reactors {

  /* specialization */

  type spec = specialized

  /** Evidence value for specialized type parameters.
   *
   *  Used to artificially insert the type into a type signature.
   */
  class Spec[@spec(Int, Long, Double) T]

  implicit val intSpec = new Spec[Int]

  implicit val longSpec = new Spec[Long]

  implicit val doubleSpec = new Spec[Double]

  private val anySpecValue = new Spec[Any]

  implicit def anySpec[T] = anySpecValue.asInstanceOf[Spec[T]]

  /* basic abstractions */

  trait Hash[@spec(Int, Long, Double) T] {
    def apply(x: T): Int
  }

  private class IntHash extends Hash[Int] {
    def apply(x: Int) = x
  }

  implicit val intHash: Hash[Int] = new IntHash

  private class LongHash extends Hash[Long] {
    def apply(x: Long) = (x ^ (x >>> 32)).toInt
  }

  implicit val longHash: Hash[Long] = new LongHash

  private class DoubleHash extends Hash[Double] {
    def apply(x: Double) = {
      val b = java.lang.Double.doubleToLongBits(x)
      (b ^ (b >>> 32)).toInt
    }
  }

  implicit val doubleHash: Hash[Double] = new DoubleHash

  private class RefHash[T <: AnyRef] extends Hash[T] {
    def apply(x: T) = x.##
  }

  implicit def refHash[T <: AnyRef]: Hash[T] = new RefHash[T]

  /* system events */

  /* exceptions */

  object exception {
    def apply(obj: Any) = throw new RuntimeException(obj.toString)
    def illegalArg(msg: String) = throw new IllegalArgumentException(msg)
    def illegalState(obj: Any) = throw new IllegalStateException(obj.toString)
    def test(obj: Any) = throw new TestControlException(obj.toString)
  }

  /** Used in tests.
   */
  case class TestControlException(msg: String)
  extends Throwable(msg) with NoStackTrace

  /** Thrown when an error in reactor execution occurs.
   */
  case class ReactorError(msg: String, cause: Throwable) extends Error(msg, cause)

  /** Thrown when an exception is propagated to an event handler, such as `onEvent`.
   */
  case class UnhandledException(cause: Throwable) extends Exception(cause)

  /** Determines if the throwable is lethal, i.e. should the program immediately stop.
   */
  def isLethal(t: Throwable): Boolean = t match {
    case e: VirtualMachineError => true
    case e: LinkageError => true
    case e: ReactorError => true
    case _ => false
  }

  /** Matches lethal throwables.
   */
  object Lethal {
    def unapply(t: Throwable): Option[Throwable] = t match {
      case e: VirtualMachineError => Some(e)
      case e: LinkageError => Some(e)
      case e: ReactorError => Some(e)
      case _ => None
    }
  }

  /** Determines if the throwable is not lethal.
   */
  def isNonLethal(t: Throwable): Boolean = !isLethal(t)

  /** Matches non-lethal throwables.
   */
  object NonLethal {
    def unapply(t: Throwable): Option[Throwable] = t match {
      case e: VirtualMachineError => None
      case e: LinkageError => None
      case e: ReactorError => None
      case _ => Some(t)
    }
  }

  /** Partial function ignores non-lethal throwables.
   *
   *  This is useful in composition with other exception handlers.
   */
  val ignoreNonLethal: PartialFunction[Throwable, Unit] = {
    case t if isNonLethal(t) => // ignore
  }

  /* URL classes for remote */

  case class SystemUrl(schema: String, host: String, port: Int) {
    @transient lazy val inetSocketAddress = Platform.inetAddress(host, port)
    @transient override val hashCode = {
      schema.hashCode + 31 * (host.hashCode + 31 * port)
    }
    def withPort(p: Int) = SystemUrl(schema, host, p)
  }
  
  case class ReactorUrl(systemUrl: SystemUrl, name: String) {
    def withPort(p: Int) = ReactorUrl(systemUrl.withPort(p), name)
  }
  
  case class ChannelUrl(reactorUrl: ReactorUrl, anchor: String) {
    @transient lazy val channelName = s"${reactorUrl.name}#$anchor"
  }

  object ChannelUrl {
    def parse(url: String): ChannelUrl = {
      var parts = url.split("://")
      val schema = parts(0)
      parts = parts(1).split("/", 2)
      val hostport = parts(0).split(":")
      val host = hostport(0)
      val port = hostport(1).toInt
      parts = parts(1).split("#")
      val reactorName = parts(0)
      val channelName = parts(1)
      ChannelUrl(ReactorUrl(SystemUrl(schema, host, port), reactorName), channelName)
    }
  }

  /* sends */

  /** Default send operations for channel objects.
   */
  implicit class LowPriorityChannelOps[T](val ch: Channel.LowPriority[T])
  extends AnyVal {
    final def !(x: T) = ch.send(x)
  }
}


package reactors {
  /** System events are a special kind of internal events that can be observed
   *  by reactors.
   */
  sealed abstract class SysEvent {
    def isReactorStarted: Boolean = false
    def isReactorTerminated: Boolean = false
    def isReactorScheduled: Boolean = false
    def isReactorPreempted: Boolean = false
    def isReactorDied: Boolean = false

    /** Returns a `Throwable` object if the event denotes an error, or `null` otherwise.
     */
    def error: Throwable = null
  }

  /** Denotes start of a reactor.
   *
   *  Produced before any other event.
   */
  case object ReactorStarted extends SysEvent {
    override def isReactorStarted = true
  }

  /** Denotes the termination of a reactor.
   *
   *  Called after all other events.
   */
  case object ReactorTerminated extends SysEvent {
    override def isReactorTerminated = true
  }

  /** Denotes that the reactor was scheduled for execution by the scheduler.
   *
   *  Always sent after `ReactorStarted` and before `ReactorTerminated`.
   *
   *  This event usually occurs when reactor is woken up to process incoming events,
   *  but may be invoked even if there are no pending events.
   *  This event is typically used in conjunction with a scheduler that periodically
   *  wakes up the reactor.
   */
  case object ReactorScheduled extends SysEvent {
    override def isReactorScheduled = true
  }

  /** Denotes that the reactor was preempted by the scheduler.
   *
   *  Always sent after `ReactorStarted` and before `ReactorTerminated`.
   *
   *  When the reactor is preempted, it loses control of the execution thread, until the
   *  scheduler schedules it again on some (possibly the same) thread.
   *  This event is typically used to send another message back to the reactor,
   *  indicating that he should be scheduled again later.
   */
  case object ReactorPreempted extends SysEvent {
    override def isReactorPreempted = true
  }

  /** Denotes that the reactor died due to an exception.
   *
   *  This event is sent after `ReactorStarted`.
   *  This event is sent before `ReactorTerminated`, *unless* the exception is thrown
   *  while `ReactorTerminated` is being processed, in which case the `ReactorDied` is
   *  not sent.
   *
   *  Note that, if the exception is thrown during the reactor constructor invocation
   *  and before the appropriate event handler is created, this event cannot be sent
   *  to that event handler.
   *
   *  @param t              the exception that the reactor threw
   */
  case class ReactorDied(t: Throwable) extends SysEvent {
    override def isReactorDied = true
    override def error = t
  }

  /** Class that describes error handlers that report uncaught reactor-level exceptions.
   */
  trait ErrorHandler extends PartialFunction[Throwable, Unit] with Platform.Reflectable

  /** The default handler prints the exception to the standard error stream.
   */
  class DefaultErrorHandler extends ErrorHandler {
    def isDefinedAt(t: Throwable): Boolean = t match {
      case t: Throwable => true
      case _ => false
    }

    def apply(t: Throwable): Unit = t match {
      case t: Throwable => t.printStackTrace()
    }
  }

  /** Silent handler ignores exceptions.
   */
  class SilentErrorHandler extends ErrorHandler {
    def isDefinedAt(t: Throwable): Boolean = t match {
      case _: Throwable => true
      case _ => false
    }

    def apply(t: Throwable): Unit = t match {
      case _: Throwable => // Do nothing.
    }
  }
}
