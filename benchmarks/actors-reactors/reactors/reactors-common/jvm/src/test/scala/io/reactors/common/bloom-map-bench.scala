package io.reactors
package common



import org.scalameter.api._
import org.scalameter.picklers.noPickler._



class BloomMapBoxingBench extends Bench.Forked[Long] {
  override def defaultConfig: Context = Context(
    exec.minWarmupRuns -> 2,
    exec.maxWarmupRuns -> 5,
    exec.independentSamples -> 1,
    verbose -> false
  )

  def measurer: Measurer[Long] =
    for (table <- Measurer.BoxingCount.allWithoutBoolean()) yield {
      table.copy(value = table.value.valuesIterator.sum)
    }

  def aggregator: Aggregator[Long] = Aggregator.median

  override def reporter = Reporter.Composite(
    LoggingReporter(),
    ValidationReporter()
  )

  val elems = (0 until 10000).map(_.toString)

  measure method "BloomMap.get/put/remove" config (
    reports.validation.predicate -> { (n: Any) => n == 0 }
  ) in {
    using(Gen.single("size")(10000)) in { size =>
      val bloom = new BloomMap[String, Int]
      var i = 0
      while (i < size) {
        bloom.put(elems(i), i)
        assert(bloom.get(elems(i)) != -1)
        i += 1
      }
      i = 0
      while (i < size) {
        bloom.remove(elems(i))
        i += 1
      }
      i = 0
      while (i < size) {
        bloom.put(elems(i), i)
        i += 1
      }
      bloom.clear()
    }
  }
}
