package io.reactors
package marshal






/** Used to annotate classes that can be automatically marshaled.
 */
trait Marshalee extends Serializable {
  def descriptor: ClassDescriptor = Platform.Reflect.descriptorOf(getClass)
}
