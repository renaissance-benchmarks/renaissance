/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm


/** Provides all of the operations of a `Ref[A]`, without the ability to get a
 *  `Ref.View`.
 *
 *  @author Nathan Bronson
 */
trait RefLike[A, Context] extends SourceLike[A, Context] with SinkLike[A, Context] {

  // read-only operations (covariant) are in SourceLike
  // write-only operations (contravariant) are in SinkLike
  // read+write operations go here 

  /** Works like `set(v)`, but returns the old value.
   *  @return the previous value of this `Ref`, as observed by `txn`.
   *  @throws IllegalStateException if `txn` is not active.
   */
  def swap(v: A)(implicit txn: Context): A

  /** Transforms the value referenced by this `Ref` by applying the function
   *  `f`.  Acts like `ref.set(f(ref.get))`, but the execution of `f` may be
   *  deferred or repeated by the STM to reduce transaction conflicts.
   *  @param f a function that is safe to call multiple times, and safe to
   *      call later during the transaction.
   *  @throws IllegalStateException if `txn` is not active.
   */
  def transform(f: A => A)(implicit txn: Context)

  /** Transforms the value referenced by this `Ref` by applying the function
   *  `f`, and returns the new value.
   *  @param f a function that is safe to call multiple times.
   *  @return the new value of this `Ref` (the value returned from `f`).
   *  @throws IllegalStateException if `txn` is not active.
   */
  def transformAndGet(f: A => A)(implicit txn: Context): A = { val z = f(get) ; set(z) ; z }

  /** Transforms the value referenced by this `Ref` by applying the function
   *  `f`, and returns the previous value.
   *  @param f a function that is safe to call multiple times.
   *  @return the previous value of this `Ref` (the value passed to `f`).
   *  @throws IllegalStateException if `txn` is not active.
   */
  def getAndTransform(f: A => A)(implicit txn: Context): A = { val z = get ; set(f(z)) ; z }

  /** Transforms the value referenced by this `Ref` from ''v'' to
   *  `f`(''v'')`._1`, and returns `f`(''v'')`._2`.
   *  @param f a function that is safe to call multiple times.
   *  @return the second element of the pair returned by `f`.
   *  @throws IllegalStateException if `txn` is not active.
   */
  def transformAndExtract[B](f: A => (A,B))(implicit txn: Context): B = { val p = f(get) ; set(p._1) ; p._2 }

  /** Transforms the value ''v'' referenced by this `Ref` by to
   *  `pf.apply`(''v''), but only if `pf.isDefinedAt`(''v'').  Returns true if
   *  a transformation was performed, false otherwise.  `pf.apply` and
   *  `pf.isDefinedAt` may be deferred or repeated by the STM to reduce
   *  transaction conflicts.
   *  @param pf a partial function that is safe to call multiple times, and
   *      safe to call later in the transaction.
   *  @return `pf.isDefinedAt(v)`, where `v` was the value of this `Ref`
   *      before transformation (if any).
   *  @throws IllegalStateException if `txn` is not active.
   */
  def transformIfDefined(pf: PartialFunction[A,A])(implicit txn: Context): Boolean

  /** Transforms the value stored in the `Ref` by incrementing it.
   *
   *  '''Note: Implementations may choose to ignore the provided `Numeric[A]`
   *  instance if `A` is a primitive type.'''
   *
   *  @param rhs the quantity by which to increment the value of this `Ref`.
   *  @throws IllegalStateException if `txn` is not active. */
  def += (rhs: A)(implicit txn: Context, num: Numeric[A]) { transform { v => num.plus(v, rhs) } }

  /** Transforms the value stored in the `Ref` by decrementing it.
   *
   *  '''Note: Implementations may choose to ignore the provided `Numeric[A]`
   *  instance if `A` is a primitive type.'''
   *
   *  @param rhs the quantity by which to decrement the value of this `Ref`.
   *  @throws IllegalStateException if `txn` is not active. */
  def -= (rhs: A)(implicit txn: Context, num: Numeric[A]) { transform { v => num.minus(v, rhs) } }

  /** Transforms the value stored in the `Ref` by multiplying it.
   *
   *  '''Note: Implementations may choose to ignore the provided `Numeric[A]`
   *  instance if `A` is a primitive type.'''
   *
   *  @param rhs the quantity by which to multiply the value of this `Ref`.
   *  @throws IllegalStateException if `txn` is not active.
   */
  def *= (rhs: A)(implicit txn: Context, num: Numeric[A]) { transform { v => num.times(v, rhs) } }

  /** Transforms the value stored the `Ref` by performing a division on it,
   *  throwing away the remainder if division is not exact for instances of
   *  type `A`.  The careful reader will note that division is actually
   *  provided by `Fractional[A]` or `Integral[A]`, it is not defined on
   *  `Numeric[A]`.  To avoid compile-time ambiguity this method accepts a
   *  `Numeric[A]` and assumes that it can be converted at runtime into
   *  either a `Fractional[A]` or an `Integral[A]`.
   *
   *  '''Note: Implementations may choose to ignore the provided `Numeric[A]`
   *  instance if `A` is a primitive type.'''
   *
   *  @param rhs the quantity by which to divide the value of this `Ref`.
   *  @throws IllegalStateException if `txn` is not active.
   */
  def /= (rhs: A)(implicit txn: Context, num: Numeric[A]) {
    num match {
      //case numF: Fractional[A] => transform { v => numF.div(v, rhs) }
      case numF: Fractional[_] => transform { v => numF.asInstanceOf[Fractional[A]].div(v, rhs) }
      //case numI: Integral[A] => transform { v => numI.quot(v, rhs) }
      case numI: Integral[_] => transform { v => numI.asInstanceOf[Integral[A]].quot(v, rhs) }
    }
  }
}
