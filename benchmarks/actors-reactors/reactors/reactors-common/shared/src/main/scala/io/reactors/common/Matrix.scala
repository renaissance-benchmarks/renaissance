package io.reactors
package common



import io.reactors.algebra.XY
import io.reactors.common.hash.spatial2D
import scala.collection._



trait Matrix[@specialized(Int, Long, Double) T] extends Matrix.Immutable[T] {
  def update(x: Int, y: Int, v: T): Unit
  def applyAndUpdate(x: Int, y: Int, v: T): T
  def remove(x: Int, y: Int): T
}


object Matrix {
  trait Immutable[@specialized(Int, Long, Double) T] {
    def apply(x: Int, y: Int): T
    def foreach(f: XY => Unit): Unit
    def copy(a: Array[T], gxf: Int, gyf: Int, gxu: Int, gyu: Int): Unit
    def area(gxf: Int, gyf: Int, gxu: Int, gyu: Int): Matrix.Area[T]
    def nonNilArea(gxf: Int, gyf: Int, gxu: Int, gyu: Int): Matrix.Area[T]
  }

  trait Action[@specialized(Int, Long, Double) T] {
    def apply(x: Int, y: Int, v: T): Unit
  }

  trait Area[@specialized(Int, Long, Double) T] {
    def foreach(a: Action[T]): Unit
  }
}
