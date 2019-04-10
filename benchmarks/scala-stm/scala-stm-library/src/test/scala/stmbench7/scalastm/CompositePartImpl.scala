/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm._
import stmbench7.core._
import stmbench7.backend.BackendFactory

class CompositePartImpl(id: Int, typ: String, buildDate: Int, documentation0: Document
        ) extends DesignObjImpl(id, typ, buildDate) with CompositePart {
  val documentation = Ref(documentation0).single
  val usedIn = Ref(List.empty[BaseAssembly]).single
  val parts = Ref(BackendFactory.instance.createLargeSet[AtomicPart]).single
  val rootPart = Ref(null : AtomicPart).single
  documentation0.setPart(this)

  def addAssembly(assembly: BaseAssembly) { usedIn.transform(assembly :: _) }

  def addPart(part: AtomicPart) = {
    val f = parts().add(part)
    if (f) {
      part.setCompositePart(this)
      if(rootPart() == null) rootPart() = part
    }
    f
  }

  def getRootPart = rootPart()
	def setRootPart(part: AtomicPart) { rootPart() = part }

  def getDocumentation = documentation()

  def getParts = parts()

  def removeAssembly(assembly: BaseAssembly ) {
    usedIn.transform { _.filterNot(_ == assembly) }
  }

  def getUsedIn = new ImmutableSeqImpl[BaseAssembly](usedIn())

  def clearPointers() {
    documentation() = null
    parts() = null
    usedIn() = null
    rootPart() = null
  }
}
