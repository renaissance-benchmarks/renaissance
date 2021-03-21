package io.reactors
package pickle



import java.io._
import java.nio.ByteBuffer



/** Pickles an object into a byte buffer, so that it can be sent over the wire.
 */
trait Pickler extends Platform.Reflectable {
  /** Pickles an object into the specified `ByteBuffer`.
   *
   *  @tparam T        type of the pickled object
   *  @param x         pickled object
   *  @param buffer    pickling target
   */
  def pickle[@spec(Int, Long, Double) T](x: T, buffer: ByteBuffer): Unit

  /** Depickles an object from the specified `ByteBuffer`.
   *
   *  @tparam T        type of the depickled object
   *  @param buffer    pickling source
   *  @return          the depickled object
   */
  def depickle[@spec(Int, Long, Double) T](buffer: ByteBuffer): T
}


object Pickler {
  private[pickle] class ByteBufferOutputStream(val buf: ByteBuffer)
  extends OutputStream {
    def write(b: Int): Unit = buf.put(b.toByte)
    override def write(bytes: Array[Byte], off: Int, len: Int): Unit = {
      buf.put(bytes, off, len)
    }
  }

  private[pickle] class ByteBufferInputStream(val buffer: ByteBuffer)
  extends InputStream {
    def read() = buffer.get()
    override def read(dst: Array[Byte], offset: Int, length: Int) = {
      val count = math.min(buffer.remaining, length)
      if (count == 0) -1
      else {
        buffer.get(dst, offset, length)
        count
      }
    }
  }
}
