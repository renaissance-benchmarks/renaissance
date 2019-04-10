/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm._
import stmbench7.core._

class ModuleImpl(id: Int, typ: String, buildDate: Int, man: Manual
        ) extends DesignObjImpl(id, typ, buildDate) with Module {

  val designRoot = Ref(null : ComplexAssembly).single

  man.setModule(this)

  def setDesignRoot(v: ComplexAssembly ) { designRoot() = v }
  def getDesignRoot = designRoot()
  def getManual = man
}
