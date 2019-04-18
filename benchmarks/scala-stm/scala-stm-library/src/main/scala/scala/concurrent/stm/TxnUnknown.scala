/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm

/** An object that represents the absence of a statically-bound current
 *  transaction.
 *  @see scala.concurrent.stm.MaybeTxn
 *
 *  @author Nathan Bronson
 */
object TxnUnknown extends MaybeTxn
