/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm._
import stmbench7.core._

abstract class AssemblyImpl(id: Int, typ: String, buildDate: Int, module0: Module, superAssembly0: ComplexAssembly
    ) extends DesignObjImpl(id, typ, buildDate) with Assembly {

  private val module = Ref(module0).single
  private val superAssembly = Ref(superAssembly0).single

  def getSuperAssembly = superAssembly()
  def getModule = module()
    
  def clearPointers() {
    superAssembly() = null
    module() = null
  }
}
