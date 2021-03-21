package io.reactors
package debugger



import scala.concurrent.Future
import scalajson.ast._



trait WebApi {
  /** Either the full state or the sequence of updates since the specified timestamp.
   *
   *  @param suid      unique identifier of the session
   *  @param ts        timestamp of the last update
   *  @param repluids  a list of REPL UIDs whose output needs to be collected
   *  @return          the state change since the last update
   */
  def state(suid: String, ts: Long, repluids: List[String]): JObject

  /** Adds a breakpoint to the debugger.
   *
   *  @param suid      unique identifier of the session
   *  @param pattern   pattern denoting whether an event matches the breakpoint
   *  @param tpe       type of the breakpoint (`reactor-started`, `reactor-died`, etc.)
   *  @return          an object indicating the breakpoint ID, or an error
   */
  def breakpointAdd(suid: String, pattern: String, tpe: String): JObject

  /** Returns the list of all the existing breakpoints.
   *
   *  @param suid      session identifier
   *  @return          an object with the list of breakpoints, or an error
   */
  def breakpointList(suid: String): JObject

  /** Removes the specified breakpoint.
   *
   *  @param suid      session identifier
   *  @param bid       breakpoint unique identifier
   *  @return          an object indicating the success, or an error
   */
  def breakpointRemove(suid: String, bid: Long): JObject

  /** Starts a new REPL.
   *
   *  @param tpe      type of the requested REPL
   *  @return         the (actual) session UID, and REPL UID
   */
  def replGet(tpe: String): Future[JValue]

  /** Evaluates a command in the REPL.
   *
   *  @param repluid  REPL UID
   *  @param command  string with the contents of the command to execute
   *  @return         the status and the output of the command
   */
  def replEval(repluid: String, cmd: String): Future[JValue]

  /** Closes the REPL.
   *
   *  @param repluid  REPL UID
   *  @return         the status and the output of the command
   */
  def replClose(repluid: String): Future[JValue]
}
