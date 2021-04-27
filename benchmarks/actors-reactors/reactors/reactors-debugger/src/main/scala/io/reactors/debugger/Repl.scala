package io.reactors
package debugger



import io.reactors.json._
import org.apache.commons.text.StringEscapeUtils
import scala.concurrent.Future
import scalajson.ast._



abstract class Repl {
  /** Unique identifier for the REPL's type.
   */
  def tpe: String

  /** Asynchronously evaluates a command in the REPL and returns the result.
   */
  def eval(cmd: String): Future[Repl.Result]

  /** Future that is completed when the REPL starts.
   */
  def started: Future[Boolean]

  /** Log something to the terminal.
   *
   *  Normally, REPL does the logging. This is called when an external entity needs to
   *  log something.
   */
  def log(x: Any): Unit

  /** Get any pending output.
   */
  def flush(): String

  /** Shuts down the REPL.
   */
  def shutdown(): Unit
}


object Repl {
  case class Result(status: Int, output: String, prompt: String, needMore: Boolean) {
    def asJson: JValue = json"""
    {
      "status": $status,
      "output": ${StringEscapeUtils.escapeJson(StringEscapeUtils.escapeJson(output))},
      "prompt": $prompt,
      "need-more": $needMore
    }
    """
  }
}
