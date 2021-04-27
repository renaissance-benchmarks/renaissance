package io.reactors
package protocol



import java.util
import org.scalatest._
import scala.collection._
import scala.collection.JavaConverters._
import org.scalatest.funsuite.AnyFunSuite



class ProtocolRegressionSpec extends AnyFunSuite {
  test("issue 64") {
    val seen = mutable.Buffer[Int]()

    util.Arrays.asList(1, 2, 3, 4, 5)
      .asScala
      .toEvents
      .map((v) => util.Arrays.asList(v, v + 1).asScala.toEvents)
      .union
      .onEvent(seen += _)

    assert(seen == Seq(1, 2, 2, 3, 3, 4, 4, 5, 5, 6))
  }
}
