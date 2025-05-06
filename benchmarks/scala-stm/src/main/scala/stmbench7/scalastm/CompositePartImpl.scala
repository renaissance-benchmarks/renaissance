/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.concurrent.stm.Ref

import stmbench7.backend.BackendFactory
import stmbench7.backend.LargeSet
import stmbench7.core.AtomicPart
import stmbench7.core.BaseAssembly
import stmbench7.core.CompositePart
import stmbench7.core.Document

class CompositePartImpl(id: Int, typ: String, buildDate: Int, documentation0: Document)
  extends DesignObjImpl(id, typ, buildDate)
  with CompositePart {

  private val documentation = Ref(documentation0).single
  private val usedIn = Ref(List.empty[BaseAssembly]).single
  private val parts = Ref(BackendFactory.instance.createLargeSet[AtomicPart]).single
  private val rootPart = Ref(null: AtomicPart).single

  documentation0.setPart(this)

  override def addAssembly(assembly: BaseAssembly): Unit = { usedIn.transform(assembly :: _) }

  override def addPart(part: AtomicPart): Boolean = {
    val f = parts().add(part)
    if (f) {
      part.setCompositePart(this)
      if (rootPart() == null) rootPart() = part
    }
    f
  }

  override def getRootPart: AtomicPart = rootPart()
  override def setRootPart(part: AtomicPart): Unit = { rootPart() = part }

  override def getDocumentation: Document = documentation()

  override def getParts: LargeSet[AtomicPart] = parts()

  override def removeAssembly(assembly: BaseAssembly): Unit = {
    usedIn.transform { _.filterNot(_ == assembly) }
  }

  override def getUsedIn = new ImmutableSeqImpl[BaseAssembly](usedIn())

  override def clearPointers(): Unit = {
    documentation() = null
    parts() = null
    usedIn() = null
    rootPart() = null
  }
}
