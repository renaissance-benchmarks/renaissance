/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm
package impl

import util.control.ControlThrowable

/** See `PendingAtomicBlock` */
private[stm] case class AlternativeResult(value: Any) extends ControlThrowable
