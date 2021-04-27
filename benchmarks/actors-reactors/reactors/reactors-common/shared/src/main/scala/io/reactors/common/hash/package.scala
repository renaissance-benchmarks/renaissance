package io.reactors.common






package object hash {

  def byteswap32(v: Int): Int = {
    var hc = v * 0x9e3775cd
    hc = java.lang.Integer.reverseBytes(hc)
    hc * 0x9e3775cd
  }

  def spatial2D(x: Int, y: Int): Int = {
    (73856093 * x) ^ (83492791 * y)
  }

}
