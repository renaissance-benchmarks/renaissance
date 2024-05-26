/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm.TSet

import stmbench7.Parameters
import stmbench7.core.Assembly
import stmbench7.core.BaseAssembly
import stmbench7.core.ComplexAssembly
import stmbench7.core.Module
import stmbench7.core.RuntimeError

class ComplexAssemblyImpl(
  id: Int,
  typ: String,
  buildDate: Int,
  module: Module,
  superAssembly: ComplexAssembly
) extends AssemblyImpl(id, typ, buildDate, module, superAssembly)
  with ComplexAssembly {

  private val subAssemblies = TSet.empty[Assembly].single

  private val level =
    if (superAssembly == null) Parameters.NumAssmLevels else superAssembly.getLevel - 1

  override def addSubAssembly(assembly: Assembly): Boolean = {
    if (assembly.isInstanceOf[BaseAssembly] && level != 2)
      throw new RuntimeError("ComplexAssembly.addAssembly: BaseAssembly at wrong level!");

    subAssemblies.add(assembly)
  }

  override def removeSubAssembly(assembly: Assembly): Boolean = subAssemblies.remove(assembly)

  override def getSubAssemblies = new ImmutableSetImpl[Assembly](subAssemblies)

  override def getLevel: Short = level.asInstanceOf[Short]

  override def clearPointers(): Unit = {
    super.clearPointers()
    subAssemblies.clear()
  }
}
