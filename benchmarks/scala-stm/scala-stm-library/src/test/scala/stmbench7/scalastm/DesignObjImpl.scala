/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm._
import stmbench7.core._

class DesignObjImpl(id: Int, typ: String, buildDate0: Int) extends DesignObj {
  val bd = Ref(buildDate0).single

	def getId = id
  def getType = typ
	def getBuildDate = bd()
	def updateBuildDate() { if (bd() % 2 == 0) bd -= 1 else bd += 1 }
	def nullOperation() {}
}
