package io.reactors.common






class Cell[@specialized(Int, Long, Double) T](private var raw: T) {
  def apply(): T = raw
  def :=(x: T): Unit = raw = x
}
