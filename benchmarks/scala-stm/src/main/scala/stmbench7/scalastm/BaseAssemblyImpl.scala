/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm.Ref

import stmbench7.core.BaseAssembly
import stmbench7.core.ComplexAssembly
import stmbench7.core.CompositePart
import stmbench7.core.Module

class BaseAssemblyImpl(
  id: Int,
  typ: String,
  buildDate: Int,
  module: Module,
  superAssembly: ComplexAssembly
) extends AssemblyImpl(id, typ, buildDate, module, superAssembly)
  with BaseAssembly {

  private val components =
    Ref(List.empty[CompositePart]).single // the original BagImpl was just an ArrayList

  override def addComponent(component: CompositePart): Unit = {
    components.transform(component :: _)
    component.addAssembly(this)
  }

  override def removeComponent(component: CompositePart): Boolean = {
    val f = components transformIfDefined {
      case x if x contains component => x filterNot { _ == component }
    }
    if (f) component.removeAssembly(this)
    f
  }

  override def getComponents = new ImmutableSeqImpl[CompositePart](components())

  override def clearPointers(): Unit = {
    super.clearPointers()
    components() = null
  }
}
