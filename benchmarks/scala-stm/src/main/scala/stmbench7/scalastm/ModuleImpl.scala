/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm.Ref

import stmbench7.core.ComplexAssembly
import stmbench7.core.Manual
import stmbench7.core.Module

class ModuleImpl(id: Int, typ: String, buildDate: Int, man: Manual)
  extends DesignObjImpl(id, typ, buildDate)
  with Module {

  private val designRoot = Ref(null: ComplexAssembly).single

  man.setModule(this)

  override def setDesignRoot(v: ComplexAssembly): Unit = { designRoot() = v }
  override def getDesignRoot: ComplexAssembly = designRoot()
  override def getManual: Manual = man
}
