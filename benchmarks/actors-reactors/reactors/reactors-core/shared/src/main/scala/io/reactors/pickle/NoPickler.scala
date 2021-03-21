package io.reactors
package pickle



import java.io._
import java.nio.ByteBuffer



/** Pickler implementation based on Java serialization.
 */
class NoPickler extends Pickler {
  def pickle[@spec(Int, Long, Double) T](x: T, buffer: ByteBuffer) =
    sys.error("Cannot pickle.")

  def depickle[@spec(Int, Long, Double) T](buffer: ByteBuffer): T =
    sys.error("Cannot depickle.")
}
