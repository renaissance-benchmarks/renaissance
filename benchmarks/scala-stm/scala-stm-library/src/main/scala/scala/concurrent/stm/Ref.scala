/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm

import impl.{RefFactory, STMImpl}
import reflect.{AnyValManifest, OptManifest}

/** `object Ref` contains factory methods that allocate an STM-managed memory
 *  location and return a `Ref` instance that provides access to that location.
 *
 *  @author Nathan Bronson
 */
object Ref extends RefCompanion {

  protected def factory: RefFactory = STMImpl.instance

  /** `Ref.View` provides access to the contents of a `Ref` without requiring
   *  that an implicit `InTxn` be available.  When called from within the
   *  dynamic scope of a transaction, `View`'s methods operate as part of that
   *  transaction.  When there is no transaction active `View`'s methods are
   *  still atomic, but only for the duration of the method call.
   *
   *  A mental model of `View` is that `view.foo(args)` acts like
   *  `atomic { implicit t => view.ref.foo(args) }`.
   */
  trait View[A] extends Source.View[A] with Sink.View[A] {

    /** Returns a `Ref` that accesses the same memory location as this view.
     *  The returned `Ref` might be the original reference that was used to
     *  construct this view, or it might be a `Ref` that is equivalent
     *  (and `==`) to the original.
     *  @return a `Ref` that accesses the same memory location as this view.
     */
    override def ref: Ref[A]

    /** Works like `set(v)`, but returns the old value.  This is an
     *  atomic swap, equivalent to atomically performing a `get`
     *  followed by `set(v)`.
     *  @return the previous value held by `ref`.
     */
    def swap(v: A): A

    /** Equivalent to atomically executing
     *  `(if (before == get) { set(after); true } else false)`, but may be more
     *  efficient, especially if there is no enclosing atomic block.
     *  @param before a value to compare against the `ref`'s contents using the
     *      value's `==` method.
     *  @param after a value to store if `before` was equal to the previous
     *      contents.
     *  @return true if `before` was equal to the previous value of the viewed
     *      `Ref`, false otherwise.
     */
    def compareAndSet(before: A, after: A): Boolean

    /** Equivalent to atomically executing
     *  `(if (before eq get) { set(after); true } else false)`, but may be more
     *  efficient, especially if there is no enclosing atomic block.
     *  @param before a value to compare against the `ref`'s contents using
     *      reference identity equality (`eq`).
     *  @param after a value to store if `before` was `eq` to the previous
     *      contents.
     *  @return true if `before` was `eq` to the previous value of the viewed
     *      `Ref`, false otherwise.
     */
    def compareAndSetIdentity[B <: A with AnyRef](before: B, after: A): Boolean

    /** Atomically replaces the value ''v'' stored in the `Ref` with
     *  `f`(''v'').  Some `Ref` implementations may defer execution of `f` or
     *  call `f` multiple times to avoid transaction conflicts.
     *  @param f a function that is safe to call multiple times, and safe to
     *      call later during the enclosing atomic block, if any.
     */
    def transform(f: A => A)

    /** Atomically replaces the value ''v'' stored in the `Ref` with
     *  `f`(''v''), returning the old value.  `transform` should be preferred
     *  if the return value is not needed, since it gives the STM more
     *  flexibility to avoid transaction conflicts.
     *  @param f a function that is safe to call multiple times, and safe to
     *      call later during any enclosing atomic block.
     *  @return the previous value of the viewed `Ref`.
     */
    def getAndTransform(f: A => A): A

    /** Atomically replaces the value ''v'' stored in the `Ref` with
     *  `f`(''v''), returning the new value.  `transform` should be preferred
     *  if the return value is not needed, since it gives the STM more
     *  flexibility to avoid transaction conflicts.
     *  @param f a function that is safe to call multiple times, and safe to
     *      call later during any enclosing atomic block.
     *  @return the new value of the viewed `Ref`.
     */
    def transformAndGet(f: A => A): A

    /** Atomically replaces the value ''v'' stored in the `Ref` with the first
     *  element of the 2-tuple returned by `f`(''v''), returning the second
     *  element.
     *  @param f a function that is safe to call multiple times.
     *  @return the second element of the tuple returned by `f`.
     */
    def transformAndExtract[B](f: A => (A,B)): B = atomic { implicit txn => ref.transformAndExtract(f) }

    /** Atomically replaces the value ''v'' stored in the `Ref` with
     *  `pf`(''v'') if `pf.isDefinedAt`(''v''), returning true, otherwise
     *  leaves the element unchanged and returns false.  `pf.apply` and
     *  `pf.isDefinedAt` might be invoked multiple times by the STM, and might
     *  be called later in any enclosing atomic block.
     *  @param pf a partial function that is safe to call multiple times, and
     *      safe to call later during any enclosing atomic block.
     *  @return `pf.isDefinedAt`(''v''), where ''v'' is the element held by
     *      this `Ref` on entry.
     */
    def transformIfDefined(pf: PartialFunction[A,A]): Boolean

    /** Transforms the value stored in the `Ref` by incrementing it.
     *
     *  '''Note: Implementations may choose to ignore the provided `Numeric[A]`
     *  instance if `A` is a primitive type.'''
     *
     *  @param rhs the quantity by which to increment the value of `ref`.
     */
    def += (rhs: A)(implicit num: Numeric[A]) { transform { v => num.plus(v, rhs) } }

    /** Transforms the value stored in the `Ref` by decrementing it.
     *
     *  '''Note: Implementations may choose to ignore the provided `Numeric[A]`
     *  instance if `A` is a primitive type.'''
     *
     *  @param rhs the quantity by which to decrement the value of `ref`.
     */
    def -= (rhs: A)(implicit num: Numeric[A]) { transform { v => num.minus(v, rhs) } }

    /** Transforms the value stored in the `Ref` by multiplying it.
     *
     *  '''Note: Implementations may choose to ignore the provided `Numeric[A]`
     *  instance if `A` is a primitive type.'''
     *
     *  @param rhs the quantity by which to multiple the value of `ref`.
     */
    def *= (rhs: A)(implicit num: Numeric[A]) { transform { v => num.times(v, rhs) } }

    /** Transforms the value stored in `ref` by performing a division on it,
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
     *  @param rhs the quantity by which to divide the value of `ref`.
     */
    def /= (rhs: A)(implicit num: Numeric[A]) {
      num match {
        //case numF: Fractional[A] => transform { v => numF.div(v, rhs) }
        case numF: Fractional[_] => transform { v => numF.asInstanceOf[Fractional[A]].div(v, rhs) }
        //case numI: Integral[A] => transform { v => numI.quot(v, rhs) }
        case numI: Integral[_] => transform { v => numI.asInstanceOf[Integral[A]].quot(v, rhs) }
      }
    }

    // If you implement a Ref.View proxy, you should define a hashCode and
    // equals that delegate to the underlying Ref or Ref.View.  Ref and
    // Ref.View that refer to the same memory location should be equal.
    //
    // override def hashCode: Int = underlying.hashCode
    // override def equals(rhs: Any): Boolean = underlying == rhs
  }
}

// All of object Ref's functionality is actually in RefCompanion.  The split
// allows RefCompanion to be tested independently of the globally configured
// RefFactory, without introducing an extra level of mutable indirection for
// normal uses of the companion object.

trait RefCompanion {
  
  protected def factory: RefFactory

  /** Returns a `Ref` instance that manages a newly allocated memory location
   *  holding values of type `A`.  If you have an initial value `v0` available,
   *  `Ref(v0)` should be preferred.
   */
  def make[A]()(implicit om: OptManifest[A]): Ref[A] = (om match {
    case m: ClassManifest[_] => m.newArray(0).asInstanceOf[AnyRef] match {
      // these can be reordered, so long as Unit comes before AnyRef
      case _: Array[Boolean] => apply(false)
      case _: Array[Byte]    => apply(0 : Byte)
      case _: Array[Short]   => apply(0 : Short)
      case _: Array[Char]    => apply(0 : Char)
      case _: Array[Int]     => apply(0 : Int)
      case _: Array[Float]   => apply(0 : Float)
      case _: Array[Long]    => apply(0 : Long)
      case _: Array[Double]  => apply(0 : Double)
      case _: Array[Unit]    => apply(())
      case _: Array[AnyRef]  => factory.newRef(null.asInstanceOf[A])(m.asInstanceOf[ClassManifest[A]])
    }
    case _ => factory.newRef(null.asInstanceOf[Any])(implicitly[ClassManifest[Any]])
  }).asInstanceOf[Ref[A]]

  /** Returns a `Ref` instance that manages a newly allocated memory location,
   *  initializing it to hold `initialValue`.  The returned `Ref` is not part
   *  of any transaction's read or write set.
   *
   *  Example: {{{
   *    val x = Ref("initial") // creates a Ref[String]
   *    val list1 = Ref(Nil : List[String]) // creates a Ref[List[String]]
   *    val list2 = Ref[List[String]](Nil)  // creates a Ref[List[String]]
   *  }}}
   */
  def apply[A](initialValue: A)(implicit om: OptManifest[A]): Ref[A] = om match {
    case m: AnyValManifest[_] => newPrimitiveRef(initialValue, m)
    case m: ClassManifest[_] => factory.newRef(initialValue)(m.asInstanceOf[ClassManifest[A]])
    case _ => factory.newRef[Any](initialValue).asInstanceOf[Ref[A]]
  }

  private def newPrimitiveRef[A](initialValue: A, m: AnyValManifest[_]): Ref[A] = {
    (m.newArray(0).asInstanceOf[AnyRef] match {
      case _: Array[Int]     => apply(initialValue.asInstanceOf[Int])
      case _: Array[Boolean] => apply(initialValue.asInstanceOf[Boolean])
      case _: Array[Byte]    => apply(initialValue.asInstanceOf[Byte])
      case _: Array[Short]   => apply(initialValue.asInstanceOf[Short])
      case _: Array[Char]    => apply(initialValue.asInstanceOf[Char])
      case _: Array[Float]   => apply(initialValue.asInstanceOf[Float])
      case _: Array[Long]    => apply(initialValue.asInstanceOf[Long])
      case _: Array[Double]  => apply(initialValue.asInstanceOf[Double])
      case _: Array[Unit]    => apply(initialValue.asInstanceOf[Unit])
    }).asInstanceOf[Ref[A]]
  }

  def apply(initialValue: Boolean): Ref[Boolean] = factory.newRef(initialValue)
  def apply(initialValue: Byte   ): Ref[Byte]    = factory.newRef(initialValue)
  def apply(initialValue: Short  ): Ref[Short]   = factory.newRef(initialValue)
  def apply(initialValue: Char   ): Ref[Char]    = factory.newRef(initialValue)
  def apply(initialValue: Int    ): Ref[Int]     = factory.newRef(initialValue)
  def apply(initialValue: Long   ): Ref[Long]    = factory.newRef(initialValue)
  def apply(initialValue: Float  ): Ref[Float]   = factory.newRef(initialValue)
  def apply(initialValue: Double ): Ref[Double]  = factory.newRef(initialValue)
  def apply(initialValue: Unit   ): Ref[Unit]    = factory.newRef(initialValue)
}

/** Provides access to a single element of type ''A''.  Accesses are
 *  performed as part of a ''memory transaction'' that comprises all of the
 *  operations of an atomic block and any nested blocks.  Single-operation
 *  memory transactions may be performed without an explicit atomic block using
 *  the `Ref.View` returned from `single`.  The software transactional memory
 *  performs concurrency control to make sure that all committed transactions
 *  are linearizable.  Reads and writes performed by a successful transaction
 *  return the same values as if they were executed instantaneously at the
 *  transaction's commit (linearization) point.
 *
 *  The static scope of an atomic block is defined by access to an implicit
 *  `InTxn` passed to the block by the STM.  Atomic blocks nest, so to
 *  participate in an atomic block for which a `InTxn` is not conveniently
 *  available, just create a new atomic block using {{{
 *    atomic { implicit t =>
 *      // the body
 *    }
 *  }}}
 *  In the static scope of an atomic block reads and writes of a `Ref`
 *  are performed by `x.get` and `x.set(v)`, or more concisely by `x()` and
 *  `x() = v`. `x.single` returns a `Ref.View` that will dynamically resolve
 *  the current scope during each method call, automatically creating a
 *  single-operation atomic block if no transaction is active.
 *
 *  It is possible for separate `Ref` instances to refer to the same element;
 *  in this case they will compare equal.  (As an example, a transactional
 *  array class might store elements in an array and create `Ref`s on demand.)
 *  `Ref`s may be provided for computed values, such as the emptiness of a
 *  queue, to allow  conditional retry and waiting on semantic properties.
 *
 *  To perform an access outside a transaction, use the view returned by
 *  `single`.  Each access through the returned view will act as if it was
 *  performed in its own single-operation transaction, dynamically nesting into
 *  an active atomic block as appropriate.
 *
 *  `Ref`'s companion object contains factory methods that create `Ref`
 *  instances paired with a single STM-managed memory location.
 *
 *  @author Nathan Bronson
 */
trait Ref[A] extends RefLike[A, InTxn] with Source[A] with Sink[A] {

  /** Returns a `Ref.View` that allows access to the contents of this `Ref`
   *  without requiring that a `InTxn` be available.  Each operation on the view
   *  will act as if it is performed in its own "single-operation" atomic
   *  block, nesting into an existing transaction if one is active.
   *
   *  A mental model of this method is that `ref.single.foo(args)` acts like
   *  `atomic { implicit t => ref.foo(args) }`.
   */
  override def single: Ref.View[A]

  // If you implement a Ref proxy, you should define a hashCode and
  // equals that delegate to the underlying Ref or Ref.View.  Ref and
  // Ref.View that refer to the same memory location should be equal.
  //
  // override def hashCode: Int = underlying.hashCode
  // override def equals(rhs: Any): Boolean = underlying == rhs
}
