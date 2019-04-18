/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm
package ccstm


private[ccstm] object Handle {

  /** A `Handle.Provider` has a single associated handle. */
  trait Provider[T] {
    def handle: Handle[T]

    override def hashCode: Int = {
      val h = handle
      CCSTM.hash(h.base, h.offset)
    }

    override def equals(rhs: Any): Boolean = {
      (this eq rhs.asInstanceOf[AnyRef]) || (rhs match {
        case r: Handle.Provider[_] => {
          val h1 = handle
          val h2 = r.handle
          (h1.base eq h2.base) && (h1.offset == h2.offset)
        }
        case r: Ref[_] => r equals this
        case v: Ref.View[_] => v equals this
        case _ => false
      })
    }
  }
}

/** A `Handle` defines the operations that must be available for a particular
 *  memory location in order for it to be managed by CCSTM.  The identity of
 *  the location is determined by `base` and `offset`, with `base` be used only
 *  in comparisons using `eq` or `ne` (no methods of `base` will ever be
 *  invoked).  Metadata is identified by `base` and `metaOffset` (the assumption
 *  made during blocking is that a write to a handle's `meta` may affect the
 *  `meta` read by any handle with the same `base` and `metaOffset`).
 *
 *  @author Nathan Bronson
 */
private[ccstm] abstract class Handle[T] {
  def meta: Long
  def meta_=(v: Long)
  def metaCAS(before: Long, after: Long): Boolean
  def base: AnyRef
  def offset: Int
  def metaOffset: Int
  def data: T
  def data_=(v: T)
}
