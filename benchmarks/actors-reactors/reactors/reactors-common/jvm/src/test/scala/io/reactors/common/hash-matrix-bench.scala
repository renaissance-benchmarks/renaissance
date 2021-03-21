package io.reactors
package common



import org.scalameter.api._
import org.scalameter.picklers.noPickler._
import org.scalameter.execution.invocation._



class HashMatrixAllocationBench extends Bench.Forked[Long] {
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
          classOf[HashMatrix.Block[String]].getName, false, true),
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

  val matrices = for (sz <- Gen.single("size")(1024)) yield {
    val hash = new HashMatrix[String](poolSize = 32)
    for (x <- 0 until sz / 64; y <- 0 until sz / 64) {
      hash(x * 32, y * 32) = ""
    }
    (sz, hash)
  }

  measure method "HashMatrix" config (
    reports.validation.predicate -> { (n: Any) => n == 0 }
  ) in {
    using(matrices) in { case (sz, hash) =>
      for (x <- 0 until sz / 64; y <- 0 until sz / 64) {
        hash(x * 32, y * 32) = hash.nil
        hash(x * 32 + sz / 2, y * 32 + sz / 2) = ""
      }
    }
  }
}
