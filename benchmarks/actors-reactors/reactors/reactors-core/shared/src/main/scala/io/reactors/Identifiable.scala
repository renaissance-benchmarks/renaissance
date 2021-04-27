package io.reactors






/** Any object that contains a unique id within some scope.
 */
trait Identifiable {
  /** Returns the unique 64-bit value of the identifiable.
   */
  def uid: Long
}
