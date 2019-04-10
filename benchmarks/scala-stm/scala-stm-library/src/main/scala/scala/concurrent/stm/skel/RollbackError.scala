/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm.skel

import util.control.ControlThrowable


/** A reusable exception instance, thrown by CCSTM when a transaction is doomed
 *  and should not continue executing.  User code should either rethrow this
 *  exception or not catch it.
 *
 *  @author Nathan Bronson
 */
private[stm] object RollbackError extends Error with ControlThrowable {
  override def fillInStackTrace(): Throwable = this
}
