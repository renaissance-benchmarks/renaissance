package io.reactors






/** Represents a data chunk.
 */
abstract class Data(
  private[reactors] val raw: Array[Byte], var startPos: Int, var endPos: Int
) {
  /** Flushes the contents of this chunk of data, and gets another one
   *  whose size is at least `minNextSize`.
   *
   *  If this data chunk belongs to a `DataBuffer`, then that `DataBuffer` is
   *  also updated.
   */
  def writeNext(minNextSize: Int): Data

  /** Acquires the next chunk of data for reading.
   *
   *  If this data chunk belongs to a `DataBuffer`, then that `DataBuffer` is
   *  also updated.
   */
  def readNext(): Data

  /** Updates this chunk of data at the position `pos`.
   */
  def update(pos: Int, b: Byte): Unit = raw(pos) = b

  /** Reads the byte at the position `pos`.
   */
  def apply(pos: Int): Byte = raw(pos)

  /** Remaining size for writing in this data chunk.
   */
  final def remainingWriteSize: Int = raw.length - endPos

  /** Remaining size for reading in this data chunk.
   */
  final def remainingReadSize: Int = endPos - startPos

  /** Total size of this data chunk.
   */
  final def totalSize: Int = raw.length

  def byteString = raw.map(b => s"$b(${b.toChar})").mkString(", ")
}
