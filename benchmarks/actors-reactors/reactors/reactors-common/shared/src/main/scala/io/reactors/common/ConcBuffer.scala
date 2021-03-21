package io.reactors.common



import scala.reflect.ClassTag



class ConcBuffer[@specialized(Int, Long, Float, Double) T: ClassTag](
  val k: Int
) {
  require(k > 0)

  private var conc: Conc[T] = Conc.Empty
  private var chunk: Array[T] = new Array(k)
  private var lastSize: Int = 0

  final def +=(elem: T): this.type = {
    if (lastSize >= k) expand()
    chunk(lastSize) = elem
    lastSize += 1
    this
  }

  private def pack() {
    conc = ConcRope.append(conc, new Conc.Chunk(chunk, lastSize, k))
  }

  private def expand() {
    pack()
    chunk = new Array(k)
    lastSize = 0
  }

  def extractConc(): Conc[T] = {
    pack()
    conc
  }
}
