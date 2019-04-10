/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm


object TxnLocal {
  /** Returns a new transaction-local that holds values of type `A`.  One
   *  `TxnLocal` instance holds a separate value for each transaction in which
   *  it has been accessed.  The value associated with a particular atomic
   *  block is created on demand, and discarded at the same time that the
   *  atomic block's after-completion handlers are invoked.  `TxnLocal` has a
   *  similar relationship to transactions as `ThreadLocal` has to threads.
   *
   *  There are two ways to specify the initial value that will be used if the
   *  first access inside a transaction is not a `set`.  If no `InTxn` context
   *  is needed to compute the initial value then the by-name parameter `init`
   *  is the most convenient.  Because this is the first parameter, you can
   *  omit the parameter name.  To construct a `TxnLocal` with a default value
   *  of `aValue`, simply {{{
   *    val tl = TxnLocal(aValue)
   *  }}}
   *  If computing the initial value requires access to `Ref`s, then it is
   *  better to use the `initialValue` parameter, which lets you write {{{
   *    val tl = TxnLocal(initialValue = { implicit txn =>
   *      // Ref reads or writes, or handler registration
   *    })
   *  }}}
   *
   *  Unlike `Ref`s, `TxnLocal`s can be read or written from inside
   *  while-preparing or while-committing callbacks, with two conditions: if
   *  the first access is from one of these callbacks then no `beforeCommit`
   *  parameter can be present; and if the first access is from one of these
   *  callbacks and it is not a write then you must use the `init`
   *  initialization method.
   *
   *  This factory method also accepts parameters that correspond to `Txn`'s
   *  transaction life-cycle handlers.  These handlers will be registered in any
   *  transaction that reads or writes the returned `TxnLocal`.  They are
   *  roughly
   *   - `beforeCommit` - the last time that `Ref`s can be read or written;
   *   - `whilePreparing` - the last time that the transaction can be rolled
   *     back;
   *   - `whileCommitting` - actions that should be atomic with respect to the
   *     transaction (keep them fast to avoid scalability issues);
   *   - `afterCommit` - called at some time after commit;
   *   - `afterRollback` - called at some time after rollback of the nesting
   *     level in which the `TxnLocal` was first accessed; and
   *   - `afterCompletion` - called either after commit or after rollback.
   *
   *  The value stored in a `TxnLocal` is subject to partial rollback: initial
   *  value computations and writes from a nested atomic block will be
   *  discarded if the block is rolled back.
   */
  def apply[A](init: => A = null.asInstanceOf[A],
               initialValue: InTxn => A = null,
               beforeCommit: InTxn => Unit = null,
               whilePreparing: InTxnEnd => Unit = null,
               whileCommitting: InTxnEnd => Unit = null,
               afterCommit: A => Unit = null,
               afterRollback: Txn.Status => Unit = null,
               afterCompletion: Txn.Status => Unit = null): TxnLocal[A] = {
    impl.STMImpl.instance.newTxnLocal(
      init, initialValue, beforeCommit, whilePreparing, whileCommitting, afterCommit, afterRollback, afterCompletion)
  }
}

/** `TxnLocal[A]` holds an instance of `A` that is local to an atomic block.
 *  See the factory method in the companion object for information about the
 *  life-cycle.
 *
 *  @author Nathan Bronson
 */
trait TxnLocal[A] extends RefLike[A, InTxnEnd] {

  /** Returns true if a value is already associated with this `TxnLocal` in the
   *  current transactional context, false otherwise.
   */
  def isInitialized(implicit txn: InTxnEnd): Boolean
}
