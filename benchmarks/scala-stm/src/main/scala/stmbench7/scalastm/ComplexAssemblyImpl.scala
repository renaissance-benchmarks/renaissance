/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm.Ref

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

  private val subAssemblies = Ref(List.empty[Assembly]).single

  private val level =
    if (superAssembly == null) Parameters.NumAssmLevels else superAssembly.getLevel - 1

  override def addSubAssembly(assembly: Assembly): Boolean = {
    if (assembly.isInstanceOf[BaseAssembly] && level != 2)
      throw new RuntimeError("ComplexAssembly.addAssembly: BaseAssembly at wrong level!")
    subAssemblies.transformIfDefined {
      case x if !x.contains(assembly) => x :+ assembly
    }
  }

  override def removeSubAssembly(assembly: Assembly): Boolean =
    subAssemblies.transformIfDefined {
      case x if x.contains(assembly) => x.filterNot(_ == assembly)
    }

  override def getSubAssemblies = new ImmutableSeqImpl[Assembly](subAssemblies())

  override def getLevel: Short = level.asInstanceOf[Short]

  override def equals(obj: Any): Boolean = obj match {
    case d: ComplexAssembly => d.getId == id
    case _ => false
  }
  override def hashCode(): Int = id

  override def clearPointers(): Unit = {
    super.clearPointers()
    subAssemblies() = null
  }
}
