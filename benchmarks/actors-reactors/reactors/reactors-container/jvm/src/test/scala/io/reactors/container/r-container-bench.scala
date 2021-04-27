package io.reactors
package container



import io.reactors.common.QuadMatrix
import org.scalameter.api._
import org.scalameter.picklers.noPickler._



class RContainerBoxingBench extends Bench.Forked[Long] {
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

  measure method "RHashMap" config (
    reports.validation.predicate -> { (n: Any) => n == 0 }
  ) in {
    using(Gen.single("numEvents")(10000)) in { numEvents =>
      val hm = new RHashMap[Int, String]

      var last17 = ""
      hm.at(17).onEvent(last17 = _)

      var i = 0
      while (i < numEvents) {
        hm(17) = "17"
        hm(i) = hm(17)
        i += 1
      }
    }
  }

  measure method "RFlatHashMap" config (
    reports.validation.predicate -> { (n: Any) => n == 0 }
  ) in {
    using(Gen.single("numEvents")(10000)) in { (numEvents) =>
      val fm = new RFlatHashMap[Int, Long]

      var lastSize = 0
      fm.sizes.onEvent(lastSize = _)

      var i = 0
      while (i < numEvents) {
        fm(17) = 19.toLong
        fm(i) = i.toLong
        if (i > numEvents / 2) fm.remove(i - 1)
        i += 1
      }
    }
  }

  measure method "RHashMatrix" config {
    reports.validation.predicate -> { (n: Any) => n == 0 }
  } in {
    using(Gen.single("numEvents")(10000)) in { numEvents =>
      val matrix = new RHashMatrix[Int]
      var i = 0
      while (i < numEvents) {
        matrix(i % 100, i / 100) = matrix(i % 10, i / 10)
        i += 1
      }

      matrix.copy(new Array(100 * 100), 0, 0, 100, 100)
    }
  }

  measure method "QuadMatrix" config {
    reports.validation.predicate -> { (n: Any) => n == 0 }
  } in {
    using(Gen.single("numEvents")(10000)) in { numEvents =>
      val matrix = new QuadMatrix[Int]
      var i = 0
      while (i < numEvents) {
        matrix(i % 100, i / 100) = matrix(i % 10, i / 10)
        i += 1
      }

      matrix.copy(new Array(100 * 100), 0, 0, 100, 100)
    }
  }

  measure method "RContainer.<combinators>" config (
    reports.validation.predicate -> { (n: Any) => n == 0 }
  ) in {
    using(Gen.single("numEvents")(10000)) in { numEvents =>
      val set = new RHashSet[Int]
      var i = 0
      while (i < numEvents) {
        set += i
        i += 1
      }

      // count
      var lastCount = 0
      set.count(_ % 2 == 0).onEvent(lastCount = _)

      // exists
      var lastExists = false
      set.exists(_ % 2 == 0).onEvent(lastExists = _)

      // forall
      var lastForall = false
      set.forall(_ % 2 == 1).onEvent(lastForall = _)

      // sizes
      var lastSize = 0
      set.sizes.onEvent(lastSize = _)

      // reduce
      var lastReduce = 0
      set.reduce(0)(_ + _)(_ - _).onEvent(lastReduce = _)

      // filter
      var lastFilter = 0
      set.filter(_ % 2 == 0).count(_ % 2 == 0).onEvent(lastFilter = _)

      // map
      var lastMap = 0
      set.map(_ + 1).count(_ % 3 == 0).onEvent(lastMap = _)

      // union
      var lastUnion = 0
      val thatSet = new RHashSet[Int]
      thatSet += 10
      thatSet += 11
      thatSet += 12
      (set union thatSet).count(_ > 5).onEvent(lastUnion = _)

      // to
      val to = set.to[RHashSet[Int]]

      i = 0
      while (i < numEvents) {
        set += i
        i += 1
      }

      while (i > 0) {
        set -= i
        i -= 1
      }
    }
  }

}
