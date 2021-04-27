package io.reactors
package common



import org.scalameter.api._
import org.scalameter.japi.JBench
import org.scalameter.japi.annotation._
import org.scalameter.picklers.noPickler._
import org.scalameter.execution.invocation._



class QuadMatrixAllocationBench extends JBench.Forked[Long] {
  override def defaultConfig: Context = Context(
    exec.minWarmupRuns -> 2,
    exec.maxWarmupRuns -> 5,
    exec.independentSamples -> 1,
    verbose -> false
  )

  def measurer: Measurer[Long] = {
    val tableMeasurer = Measurer.MethodInvocationCount(
      new InvocationCountMatcher(
        InvocationCountMatcher.ClassMatcher.Descendants(
          classOf[QuadMatrix.Node[String]].getName, false, false),
        InvocationCountMatcher.MethodMatcher.Allocation))
    for (table <- tableMeasurer) yield {
      table.copy(value = table.value.valuesIterator.sum)
    }
  }

  def aggregator: Aggregator[Long] = Aggregator.max

  override def reporter = Reporter.Composite(
    LoggingReporter(),
    ValidationReporter()
  )

  val fullMatrices = for (sz <- Gen.single("size")(64)) yield {
    val quad = new QuadMatrix[String](poolSize = 1024)
    for (x <- 0 until sz / 3; y <- 0 until sz / 3) {
      quad(x * 3, y * 3) = ""
    }
    quad.fillPools()
    (sz, quad)
  }

  val matrices = for (sz <- Gen.single("size")(64)) yield {
    val quad = new QuadMatrix[String](poolSize = 32)
    for (x <- 0 until sz / 2; y <- 0 until sz / 2) {
      quad(x, y) = ""
    }
    (sz, quad)
  }

  val fullPoolCtx = Context(
    reports.validation.predicate -> { (n: Any) => n == 0 }
  )

  @gen("fullMatrices")
  @benchmark("QuadMatrix.full-pool")
  @curve("Matrix")
  @ctx("fullPoolCtx")
  def fullPool(t: (Int, QuadMatrix[String])) {
    val (sz, quad) = t
    for (x <- 0 until sz; y <- 0 until sz) {
      quad(x, y) = ""
    }
  }

  val emptyPoolCtx = Context(
    reports.validation.predicate -> { (n: Any) => n == 15 }
  )

  @gen("matrices")
  @benchmark("QuadMatrix.empty-pool")
  @curve("Matrix")
  @ctx("emptyPoolCtx")
  def emptyPool(t: (Int, QuadMatrix[String])) {
    val (sz, quad) = t
    for (x <- 0 until sz / 2; y <- 0 until sz / 2) {
      quad.remove(x, y)
      quad(x + sz / 2, y + sz / 2) = ""
    }
  }

}
