/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm._
import stmbench7.core._
import stmbench7.backend.IdPool

object IdPoolImpl {
  class BoxedList(n: Int) extends IdPool {
    val underlying = Ref(List.range(1, n + 1)).single
    
    def putUnusedId(id: Int) { underlying.transform(id :: _) }

    def getId = {
      underlying.getAndTransform(_.drop(1)) match {
        case head :: _ => head
        case _ => throw new OperationFailedException
      }
    }
  }
}