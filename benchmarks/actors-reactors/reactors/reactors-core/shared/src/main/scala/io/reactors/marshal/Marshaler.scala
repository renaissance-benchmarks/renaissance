package io.reactors
package marshal





trait Marshaler[@spec(Int, Long, Double) T] {
  def marshal(x: T, data: Data): Unit
  def unmarshal(data: Data): T
}
