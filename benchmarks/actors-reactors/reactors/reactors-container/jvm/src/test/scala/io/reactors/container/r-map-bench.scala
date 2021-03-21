package io.reactors
package container



import org.scalameter.api._
import org.scalameter.picklers.noPickler._



class RMapBoxingBench extends Bench.Forked[Long] {
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

  measure method "RMap.<combinators>" config (
    reports.validation.predicate -> { (n: Any) => n == 0 }
  ) in {
    using(Gen.single("numEvents")(10000)) in { numEvents =>
      val table = new RHashMap[Int, String]
      var i = 0
      while (i < numEvents) {
        table(i) = ""
        i += 1
      }

      // collectValue
      val longstrings = table.collectValue {
        case s if s.length > 1 => s
      }.toMap[RHashMap[Int, String]]

      // RMap.apply
      val lengths = RMap[RFlatHashMap[Int, Int]] { m =>
        new RMap.On(table) {
          def insert(k: Int, v: String) = m(k) = v.length
          def remove(k: Int, v: String) = m.remove(k)
        }
      }

      i = 0
      while (i < numEvents) {
        table(i) = ""
        i += 1
      }

      while (i > 0) {
        table.remove(i)
        i -= 1
      }
    }
  }

}
