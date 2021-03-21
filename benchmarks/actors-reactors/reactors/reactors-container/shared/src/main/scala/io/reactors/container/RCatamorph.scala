package io.reactors
package container






/** Reactive catamorphs are containers that maintain the aggregation of their elements.
 *
 *  @tparam T       type of the aggregation
 *  @tparam S       type of the elements
 */
trait RCatamorph[@spec(Int, Long, Double) T, @spec(Int, Long, Double) S]
extends RContainer[S] {

  def +=(v: S): Boolean

  def -=(v: S): Boolean

  def push(v: S): Boolean

  def signal: Signal[T]

}
