package io.reactors






abstract class DataBuffer {
  /** Clears the contents of the data buffer.
   */
  def clear(): Unit

  /** The writing end of the buffer.
   */
  def output: Data

  /** The reading end of the buffer.
   */
  def input: Data

  /** Indicates whether this buffer has bytes available to read.
   */
  def hasMore: Boolean

  /** Optionally flushes the contents of this data buffer, depending on the semantics.
   */
  def flush(): Unit = {
  }
}


object DataBuffer {
  def streaming(batchSize: Int): DataBuffer = new Linked(batchSize)

  private[reactors] class Linked(val initialBatchSize: Int) extends DataBuffer {
    private[reactors] var rawOutput = allocateData(initialBatchSize)
    private[reactors] var rawInput = rawOutput

    protected[reactors] def allocateData(minNextSize: Int): LinkedData = {
      new LinkedData(this, math.max(initialBatchSize, minNextSize))
    }

    protected[reactors] def deallocateData(old: LinkedData) = {
    }

    protected[reactors] def onWriteNext(old: LinkedData): Unit = {
      rawOutput = old.next
    }

    protected[reactors] def onReadNext(old: LinkedData): Unit = {
      rawInput = old.next
    }

    def clear(): Unit = {
      rawOutput = allocateData(initialBatchSize)
      rawInput = rawOutput
    }

    def output: Data = rawOutput

    def input: Data = rawInput

    def hasMore: Boolean = {
      rawInput == rawOutput && rawInput.remainingReadSize == 0
    }
  }

  private[reactors] class LinkedData(
    private var rawBuffer: Linked,
    rawArray: Array[Byte]
  ) extends Data(rawArray, 0, 0) {
    private[reactors] var next: LinkedData = null

    def this(buffer: Linked, requestedBatchSize: Int) =
      this(buffer, new Array[Byte](requestedBatchSize))

    def buffer: Linked = rawBuffer

    private[reactors] def buffer_=(sb: Linked) = rawBuffer = sb

    def writeNext(minNextSize: Int): Data = {
      next = buffer.allocateData(minNextSize)
      val result = next
      buffer.onWriteNext(this)
      result
    }

    def readNext(): Data = {
      val result = next
      if (result != null) {
        buffer.onReadNext(this)
        buffer.deallocateData(this)
      }
      // After this point, the `Data` object is potentially deallocated
      // and must not be used again.
      result
    }

    def fullByteString: String = {
      var curr = buffer.rawInput
      var s = ""
      while (curr != null) {
        s += curr.byteString + "\n -> "
        curr = curr match {
          case linked: DataBuffer.LinkedData => linked.next
          case _ => null
        }
      }
      s
    }
  }
}
