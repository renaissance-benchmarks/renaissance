package io.reactors
package pickle



import java.io._
import java.nio.ByteBuffer



/** Pickler implementation based on Java serialization.
 */
class JavaSerializationPickler extends Pickler {
  def pickle[@spec(Int, Long, Double) T](x: T, buffer: ByteBuffer) = {
    val os = new Pickler.ByteBufferOutputStream(buffer)
    val oos = new ObjectOutputStream(os)
    oos.writeObject(x)
  }

  def depickle[@spec(Int, Long, Double) T](buffer: ByteBuffer): T = {
    val is = new Pickler.ByteBufferInputStream(buffer)
    val ois = new ObjectInputStream(is)
    ois.readObject().asInstanceOf[T]
  }
}
