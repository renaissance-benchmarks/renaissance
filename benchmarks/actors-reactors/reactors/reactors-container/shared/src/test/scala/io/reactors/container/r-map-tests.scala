package io.reactors
package container



import org.scalacheck._
import org.scalacheck.Gen._
import org.scalacheck.Prop._
import io.reactors.test._
import scala.collection._



class RMapCheck extends Properties("RMap") with ExtendedProperties {

  val sizes = detChoose(0, 500)

  val seeds = detChoose(0, 1000000)

  def randomInts(until: Int) = for (sz <- sizes; seed <- seeds) yield {
    val rng = new scala.util.Random(seed)
    for (i <- 0 until sz) yield rng.nextInt(until)
  }

  property("collectValue") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val table = new RHashMap[Int, String]
      val longStrings = table.collectValue {
        case s if s.length > 2 => s
      }.toMap[RHashMap[Int, String]]
      val seen = mutable.Set[Int]()
      longStrings.inserts.onEvent(seen += _)
      for (i <- 0 until sz) table(i) = i.toString
      assert(seen == (100 until sz).toSet)
      seen.clear()
      for (k <- longStrings) seen += k
      seen == (100 until sz).toSet
    }
  }

  property("RMap.apply") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val table = new RHashMap[Int, String]
      val lengths = RMap[RFlatHashMap[Int, Int]] { m =>
        new RMap.On(table) {
          def insert(k: Int, v: String) = m(k) = v.length
          def remove(k: Int, v: String) = m.remove(k)
        }
      }
      val numbers = 0 until sz
      for (i <- numbers) table(i) = i.toString
      val seen = mutable.Map[Int, Int]()
      for (k <- lengths) seen(k) = lengths(k)
      seen == numbers.zip(numbers.map(_.toString.length)).toMap
    }
  }

  property("emit modified on collected values") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val table = new RHashMap[Int, String]
      val collected = table.collectValue {
        case "9" => "9"
      }
      var timesModified = 0
      collected.modified.onEvent { _ =>
        timesModified += 1
      }
      assert(timesModified == 0)
      for (i <- 0 until sz) {
        table(i) = (i % 10).toString
        assert(timesModified == (i + 1) / 10)
      }
      true
    }
  }

  property("emit adds") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val table = new RHashMap[Int, String]
      var totalAdds = 0
      table.adds.on(totalAdds += 1)
      for (i <- 0 until sz) {
        assert(totalAdds == i)
        table(i) = i.toString
      }
      assert(totalAdds == sz)
      for (i <- 0 until sz) {
        assert(totalAdds == sz)
        table(i) = (-i).toString
      }
      true
    }
  }

  property("emit updates") = forAllNoShrink(sizes) { sz =>
    stackTraced {
      val table = new RHashMap[Int, String]
      var totalUpdates = 0
      table.updates.on(totalUpdates += 1)
      for (i <- 0 until sz) {
        assert(totalUpdates == 0)
        table(i) = i.toString
      }
      assert(totalUpdates == 0)
      for (i <- 0 until sz) {
        assert(totalUpdates == i)
        table(i) = (-i).toString
      }
      assert(totalUpdates == sz)
      true
    }
  }

}
