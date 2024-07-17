/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package stmbench7.scalastm

import scala.annotation.unused

import scala.concurrent.stm.atomic
import scala.concurrent.stm.Ref

import stmbench7.OperationExecutor
import stmbench7.OperationExecutorFactory
import stmbench7.Parameters
import stmbench7.SynchMethodInitializer
import stmbench7.ThreadFactory
import stmbench7.backend.BackendFactory
import stmbench7.backend.IdPool
import stmbench7.backend.Index
import stmbench7.backend.LargeSet
import stmbench7.core.AtomicPart
import stmbench7.core.ComplexAssembly
import stmbench7.core.DesignObjFactory
import stmbench7.core.Document
import stmbench7.core.Manual
import stmbench7.core.Module
import stmbench7.core.Operation
import stmbench7.impl.core.ConnectionImpl

@unused("Referenced via string name")
class ScalaSTMInitializer extends SynchMethodInitializer {

  def createOperationExecutorFactory(): OperationExecutorFactory =
    new OperationExecutorFactory {

      private val timestamp = Ref(0)

      def createOperationExecutor(op: Operation): OperationExecutor =
        new OperationExecutor {
          private var lastTS = 0

          def execute(): Int = {
            atomic { implicit t =>
              val z = op.performOperation()
              if (Parameters.sequentialReplayEnabled) {
                timestamp += 1
                lastTS = timestamp()
              }
              z
            }
          }

          def getLastOperationTimestamp: Int = lastTS
        }
    }

  def createBackendFactory(): BackendFactory =
    new BackendFactory {

      // a couple hundred, not ordered, except for huge numbers of discarded
      // sets with exactly 1 element
      def createLargeSet[E <: Comparable[E]](): LargeSet[E] = new LargeSetImpl[E]

      // ordered
      def createIndex[K <: Comparable[K], V](): Index[K, V] = new IndexImpl.BoxedImmutable[K, V]

      def createIdPool(maxNumberOfIds: Int): IdPool = new IdPoolImpl.BoxedList(maxNumberOfIds)
    }

  def createDesignObjFactory(): DesignObjFactory =
    new DesignObjFactory {

      def createAtomicPart(id: Int, typ: String, bd: Int, x: Int, y: Int) =
        new AtomicPartImpl(id, typ, bd, x, y)

      def createConnection(from: AtomicPart, to: AtomicPart, typ: String, length: Int) =
        new ConnectionImpl(from, to, typ, length)

      def createBaseAssembly(
        id: Int,
        typ: String,
        buildDate: Int,
        module: Module,
        superAssembly: ComplexAssembly
      ) =
        new BaseAssemblyImpl(id, typ, buildDate, module, superAssembly)

      def createComplexAssembly(
        id: Int,
        typ: String,
        buildDate: Int,
        module: Module,
        superAssembly: ComplexAssembly
      ) =
        new ComplexAssemblyImpl(id, typ, buildDate, module, superAssembly)

      def createCompositePart(id: Int, typ: String, buildDate: Int, documentation: Document) =
        new CompositePartImpl(id, typ, buildDate, documentation)

      def createDocument(id: Int, title: String, text: String) =
        new DocumentImpl(id, title, text)

      def createManual(id: Int, title: String, text: String) =
        new ManualImpl(id, title, text)

      def createModule(id: Int, typ: String, buildDate: Int, man: Manual) =
        new ModuleImpl(id, typ, buildDate, man)
    }

  def createThreadFactory(): ThreadFactory =
    (body: Runnable) => new Thread(body)
}
