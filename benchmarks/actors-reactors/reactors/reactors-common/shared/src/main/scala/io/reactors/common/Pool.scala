package io.reactors
package common



import scala.reflect.ClassTag



abstract class Pool[T >: Null <: AnyRef] {
  def acquire(): T
  def release(x: T): Unit
}


object Pool {
  class Zero[T >: Null <: AnyRef](
    val create: () => T,
    val onRelease: T => Unit
  ) extends Pool[T] {
    def acquire(): T = create()
    def release(x: T): Unit = {}
  }
}
