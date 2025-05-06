/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm.Ref

import stmbench7.core.DesignObj

class DesignObjImpl(id: Int, typ: String, buildDate0: Int) extends DesignObj {
  private val bd = Ref(buildDate0).single

  override def getId: Int = id
  override def getType: String = typ
  override def getBuildDate: Int = bd()
  override def updateBuildDate(): Unit = { if (bd() % 2 == 0) bd -= 1 else bd += 1 }
  override def nullOperation(): Unit = {}
}
