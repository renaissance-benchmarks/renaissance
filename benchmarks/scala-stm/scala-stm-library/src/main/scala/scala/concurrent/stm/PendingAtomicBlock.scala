/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm

/** Instances of `PendingAtomicBlock` defer the execution of an atomic block
 *  until all of the alternatives can be gathered from the user.  There is an
 *  implicit conversion in the `stm` package object from any type `A` to a
 *  `PendingAtomicBlock[A]`, which will kick in if there is an attempt to call
 *  `.orAtomic` on a value.
 *
 *  @author Nathan Bronson
 */
class PendingAtomicBlock[A](above: => A) {

  /** See `atomic.oneOf`. */
  def orAtomic[B >: A](below: InTxn => B)(implicit mt: MaybeTxn): B = {
    // Execution of Delayed.orAtomic proceeds bottom to top, with the upper
    // portions being captured by-name in `above`.  The actual transactional
    // execution is all performed inside the top-most block (the one that
    // used atomic rather than orAtomic).  If a block other than the top one
    // is the one that eventually succeeds, we must tunnel the value out with
    // an exception because the alternatives may have a wider type.  We only
    // catch the exception if we are the bottom-most alternative, because
    // only it is guaranteed to have been fully widened.
    if (!atomic.pushAlternative(mt, below)) {
      // we're not the bottom
      above
    } else {
      // we're the bottom, this is the end of the result tunnel
      try {
        above
      } catch {
        case impl.AlternativeResult(x) => x.asInstanceOf[B]
      }
    }
  }
}
