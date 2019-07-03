package cafesat.util

import scala.annotation.implicitNotFound

/*
 * Logging should be used for extra information, not serving as a reporting tool for the
 * tool usage. In particular, in a CLI style of use, we should use stdin and stdout for
 * regular input-output (sat/unsat, model printing depending on arguments, etc), and logging
 * should be sent to a different stream (and be configurable or turned off). logging level
 * INFO is not to be used for regular output of the system (again, like sat/unsat).
 *
 * Choice of logging level is as follows: TODO
 *
 */

object Logger {

  sealed trait LogLevel extends Ordered[LogLevel] {
    val ordinal: Int

    override def compare(ll: LogLevel): Int = ordinal - ll.ordinal
  }
  //TODO: not sure about that name, but if one uses this to define logLevel then there won't
  //be any logging
  object NoLogging extends LogLevel {
    override val ordinal = -1
  }
  object Error extends LogLevel {
    override val ordinal = 0
  }
  object Warning extends LogLevel {
    override val ordinal = 1
  }
  object Info extends LogLevel {
    override val ordinal = 2
  }
  object Debug extends LogLevel {
    override val ordinal = 3
  }
  object Trace extends LogLevel {
    override val ordinal = 4
  }

  @implicitNotFound("No implicit logger tag found in scope. You need define an implicit util.Logger.Tag")
  case class Tag(val name: String)
}

abstract class Logger {

  import Logger._

  private val errorPrefix   = "[ Error ] "
  private val warningPrefix = "[Warning] "
  private val infoPrefix    = "[ Info  ] "
  private val debugPrefix   = "[ Debug ] "
  private val tracePrefix   = "[ Trace ] "

  def output(msg: String): Unit

  def logLevel: LogLevel

  protected def reline(prefix: String, tag: Tag, msg: String): String = {
    val colorPrefix = 
      if(prefix == errorPrefix) 
        Console.RED
      else if(prefix == warningPrefix) 
        Console.YELLOW
      else if(prefix == debugPrefix)
        Console.MAGENTA
      else if(prefix == tracePrefix)
        Console.GREEN
      else //for INFO
        Console.BLUE
    val colorTag = Console.CYAN
    "[" + colorPrefix + prefix.substring(1, prefix.length-2) + Console.RESET + "] " +
    "[ " + colorTag + tag.name + Console.RESET + " ] " +
    msg.trim.replaceAll("\n", "\n" + (" " * (prefix.size)))
  }

  def error(msg: => String)(implicit tag: Tag) = if(logLevel >= Error) output(reline(errorPrefix, tag, msg))
  def warning(msg: => String)(implicit tag: Tag) = if(logLevel >= Warning) output(reline(warningPrefix, tag, msg))
  def info(msg: => String)(implicit tag: Tag) = if(logLevel >= Info) output(reline(infoPrefix, tag, msg))
  def debug(msg: => String)(implicit tag: Tag) = if(logLevel >= Debug) output(reline(debugPrefix, tag, msg))
  def trace(msg: => String)(implicit tag: Tag) = if(logLevel >= Trace) output(reline(tracePrefix, tag, msg))

}

object SilentLogger extends Logger {
  //not sure, but it seems redundant ot override both output and log level
  //to state the same thing

  override def output(msg: String): Unit = {}

  override val logLevel: Logger.LogLevel = Logger.NoLogging
}

//The usual policy is to use the standard error to log
//the information
abstract class StdErrLogger extends Logger {
  override def output(msg: String): Unit = {
    Console.err.println(msg)
  }
}

object ErrorStdErrLogger extends StdErrLogger {

  import Logger._

  override val logLevel: LogLevel = Error
}

object DefaultStdErrLogger extends StdErrLogger {

  import Logger._

  override val logLevel: LogLevel = Warning
}

object InfoStdErrLogger extends StdErrLogger {

  import Logger._

  override val logLevel: LogLevel = Info
}

object VerboseStdErrLogger extends StdErrLogger {

  import Logger._

  override val logLevel: LogLevel = Debug
}

object TraceStdErrLogger extends StdErrLogger {

  import Logger._

  override val logLevel: LogLevel = Trace
}
