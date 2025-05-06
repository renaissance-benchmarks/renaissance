/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm.Ref

import stmbench7.backend.IdPool
import stmbench7.core.OperationFailedException

object IdPoolImpl {

  class BoxedList(n: Int) extends IdPool {
    private val underlying = Ref(List.range(1, n + 1)).single

    override def putUnusedId(id: Int): Unit = { underlying.transform(id :: _) }

    override def getId: Int = {
      underlying.getAndTransform(_.drop(1)) match {
        case head :: _ => head
        case _ => throw new OperationFailedException
      }
    }
  }
}
