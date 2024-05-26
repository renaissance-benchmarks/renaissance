/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm.Ref

import stmbench7.core.Assembly
import stmbench7.core.ComplexAssembly
import stmbench7.core.Module

abstract class AssemblyImpl(
  id: Int,
  typ: String,
  buildDate: Int,
  module0: Module,
  superAssembly0: ComplexAssembly
) extends DesignObjImpl(id, typ, buildDate)
  with Assembly {

  private val module = Ref(module0).single
  private val superAssembly = Ref(superAssembly0).single

  override def getSuperAssembly: ComplexAssembly = superAssembly()
  override def getModule: Module = module()

  override def clearPointers(): Unit = {
    superAssembly() = null
    module() = null
  }
}
