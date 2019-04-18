/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm


/** Provides all of the operations of a `Source[A]`, without the ability to get
 *  a `Source.View`.
 *
 *  @author Nathan Bronson
 */
trait SourceLike[+A, Context] {

  /** Performs a transactional read and checks that it is consistent with all
   *  reads already made by `txn`.  Equivalent to `get`.
   *
   *  Example: {{{
   *    val x = Ref(0)
   *    atomic { implicit t =>
   *      ...
   *      val v = x() // perform a read inside a transaction
   *      ...
   *    }
   *  }}}
   *  @param txn an active transaction.
   *  @return the value of the `Ref` as observed by `txn`.
   *  @throws IllegalStateException if `txn` is not active.
   */
  def apply()(implicit txn: Context): A = get
  
  /** Performs a transactional read and checks that it is consistent with all
   *  reads already made by `txn`.  Equivalent to `apply()`, which is more
   *  concise in many situations.
   *  @param txn an active transaction.
   *  @return the value of the `Ref` as observed by `txn`.
   *  @throws IllegalStateException if `txn` is not active.
   */
  def get(implicit txn: Context): A

  /** Returns `f(get)`, possibly reevaluating `f` to avoid rollback if a
   *  conflicting change is made but the old and new values are equal after
   *  application of `f`.  Requires that `f(x) == f(y)` if `x == y`.
   *
   *  `getWith(f)` is equivalent to `f(relaxedGet({ f(_) == f(_) }))`, although
   *  perhaps more efficient.
   *  @param f an idempotent function.
   *  @return the result of applying `f` to the value contained in this `Ref`.
   */
  def getWith[Z](f: A => Z)(implicit txn: Context): Z

  /** Returns the same value as `get`, but allows the caller to determine
   *  whether `txn` should be rolled back if another thread changes the value
   *  of this `Ref` before `txn` is committed.  If `ref.relaxedGet(equiv)`
   *  returns `v0` in `txn`, another context changes `ref` to `v1`, and
   *  `equiv(v0, v1) == true`, then `txn` won't be required to roll back (at
   *  least not due to this read).  If additional changes are made to `ref`
   *  additional calls to the equivalence function will be made, always with
   *  `v0` as the first parameter.
   *
   *  `equiv` will always be invoked on the current thread.  Extreme care
   *  should be taken if the equivalence function accesses any `Ref`s.
   *
   *  As an example, to perform a read that will not be validated during commit
   *  you can use the maximally permissive equivalence function: {{{
   *    val unvalidatedValue = ref.relaxedGet({ (_, _) => true })
   *  }}}
   *  To check view serializability rather than conflict serializability for a
   *  read: {{{
   *    val viewSerializableValue = ref.relaxedGet({ _ == _ })
   *  }}}
   *  The `getWith` method provides related functionality.
   *  @param equiv an equivalence function that returns true if a transaction
   *      that observed the first argument will still complete correctly,
   *      where the second argument is the actual value that should have been
   *      observed.
   *  @return a value of the `Ref`, not necessary consistent with the rest of
   *      the reads performed by `txn`.
   */
  def relaxedGet(equiv: (A, A) => Boolean)(implicit txn: Context): A
}
