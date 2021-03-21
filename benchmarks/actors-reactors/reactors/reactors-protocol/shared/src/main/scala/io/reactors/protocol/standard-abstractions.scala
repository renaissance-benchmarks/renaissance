package io.reactors
package protocol






trait StandardAbstractions


/** Represents a stamped object.
 *
 *  @tparam T    type of the stamped object
 */
sealed trait Stamp[T] {
  def isEmpty: Boolean
  def nonEmpty: Boolean
  def stamp: Long
}


object Stamp {
  /** The empty case of a stamped value.
   */
  case class None[T]() extends Stamp[T] {
    def isEmpty = true
    def nonEmpty = false
    def stamp = -1
  }

  /** Non-empty case of the stamped value.
   *
   * @param x       the underlying object
   * @param stamp   the stamp of this stamped value
   */
  case class Some[T](x: T, stamp: Long) extends Stamp[T] {
    def isEmpty = false
    def nonEmpty = true
  }
}
