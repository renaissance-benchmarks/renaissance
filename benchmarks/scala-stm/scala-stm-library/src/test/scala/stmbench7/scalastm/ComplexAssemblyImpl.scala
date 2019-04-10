/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm._
import stmbench7.core._
import stmbench7.Parameters

class ComplexAssemblyImpl(id: Int, typ: String, buildDate: Int, module: Module, superAssembly: ComplexAssembly
        ) extends AssemblyImpl(id, typ, buildDate, module, superAssembly) with ComplexAssembly {

  val subAssemblies = TSet.empty[Assembly].single
  val level = if (superAssembly == null) Parameters.NumAssmLevels else superAssembly.getLevel - 1

  def addSubAssembly(assembly: Assembly) = {
    if(assembly.isInstanceOf[BaseAssembly] && level != 2)
      throw new RuntimeError("ComplexAssembly.addAssembly: BaseAssembly at wrong level!");
    	
    subAssemblies.add(assembly)
  }

  def removeSubAssembly(assembly: Assembly) = subAssemblies.remove(assembly)

  def getSubAssemblies = new ImmutableSetImpl[Assembly](subAssemblies)

  def getLevel = level.asInstanceOf[Short]

  override def clearPointers() {
    super.clearPointers()
    subAssemblies.clear()
  }
}
