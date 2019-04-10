/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm
package impl

import scala.collection.mutable.Builder

/** `RefFactory` is responsible for creating concrete `Ref` instances. */ 
trait RefFactory {
  def newRef(v0: Boolean): Ref[Boolean]
  def newRef(v0: Byte):    Ref[Byte]
  def newRef(v0: Short):   Ref[Short]
  def newRef(v0: Char):    Ref[Char]
  def newRef(v0: Int):     Ref[Int]
  def newRef(v0: Float):   Ref[Float]
  def newRef(v0: Long):    Ref[Long]
  def newRef(v0: Double):  Ref[Double]
  def newRef(v0: Unit):    Ref[Unit]

  /** `T` will not be one of the primitive types (for which a `newRef`
   *  specialization exists).
   */ 
  def newRef[A : ClassManifest](v0: A): Ref[A]

  def newTxnLocal[A](init: => A,
                     initialValue: InTxn => A,
                     beforeCommit: InTxn => Unit,
                     whilePreparing: InTxnEnd => Unit,
                     whileCommitting: InTxnEnd => Unit,
                     afterCommit: A => Unit,
                     afterRollback: Txn.Status => Unit,
                     afterCompletion: Txn.Status => Unit): TxnLocal[A]

  def newTArray[A : ClassManifest](length: Int): TArray[A]
  def newTArray[A : ClassManifest](xs: TraversableOnce[A]): TArray[A]

  def newTMap[A, B]: TMap[A, B]
  def newTMapBuilder[A, B]: Builder[(A, B), TMap[A, B]]

  def newTSet[A]: TSet[A]
  def newTSetBuilder[A]: Builder[A, TSet[A]]
}
