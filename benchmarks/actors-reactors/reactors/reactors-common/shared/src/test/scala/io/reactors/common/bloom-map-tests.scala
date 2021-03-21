package io.reactors.common



import io.reactors.test._
import org.scalacheck._
import org.scalacheck.Prop.forAllNoShrink
import scala.collection._
import scala.util.Random



class BloomMapCheck extends Properties("BloomMap") with ExtendedProperties {

  val sizes = detChoose(1, 2048)

  property("put and check key-value pairs") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val map = new BloomMap[String, String]

      val elems = (0 to size).map(_.toString)
      for (i <- 0 until size) {
        map.put(elems(i), elems(i))
        assert(map.contains(elems(i)))
        assert(map.get(elems(i)) == elems(i))
        val next = i + 1
        assert(!map.contains(elems(next)))
        assert(map.get(elems(next)) == null)
      }

      for (i <- 0 until size) assert(map.contains(elems(i)))

      true
    }
  }

  property("remove and check key-value pairs") = forAllNoShrink(sizes) { size =>
    stackTraced {
      val map = new BloomMap[String, String]

      val elems = (0 to size).map(x => "num: " + x)
      for (i <- 0 until size) {
        map.put(elems(i), elems(i))
        assert(map.contains(elems(i)))
      }
      for (i <- 0 until size) {
        assert(map.contains(elems(i)), i)
        assert(map.remove(elems(i)) == elems(i))
        assert(!map.contains(elems(i)))
      }

      true
    }
  }
}
