package io.reactors
package marshal






/** Used to implement classes with custom marshaling.
 */
trait Marshalable extends Marshalee {
  def marshal(data: Data): Unit
  def unmarshal(data: Data): Unit
}
