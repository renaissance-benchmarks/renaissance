/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm


/** Provides all of the operations of a `Sink[A]`, without the ability to get
 *  a `Sink.View`.
 *
 *  @author Nathan Bronson
 */
trait SinkLike[-A, Context] {

  /** Performs a transactional write.  The new value will not be visible by
   *  any other threads until (and unless) `txn` successfully commits.
   *  Equivalent to `set(v)`.
   *
   *  Example: {{{
   *    val x = Ref(0)
   *    atomic { implicit t =>
   *      ...
   *      x() = 10 // perform a write inside a transaction
   *      ...
   *    }
   *  }}}
   *  @param v a value to store in the `Ref`.
   *  @throws IllegalStateException if `txn` is not active. */
  def update(v: A)(implicit txn: Context) { set(v) }

  /** Performs a transactional write.  The new value will not be visible by
   *  any other threads until (and unless) `txn` successfully commits.
   *  Equivalent to `update(v)`.
   *  @param v a value to store in the `Ref`.
   *  @throws IllegalStateException if `txn` is not active.
   */
  def set(v: A)(implicit txn: Context)

  /** Performs a transactional write and returns true, or returns false.  The
   *  STM implementation may choose to return false to reduce (not necessarily
   *  avoid) blocking.  If no other threads are performing any transactional or
   *  atomic accesses then this method will succeed. 
   */
  def trySet(v: A)(implicit txn: Context): Boolean
}
