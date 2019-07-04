package cafesat.parsers

import java.io.Reader
import java.io.StringReader

import org.scalatest.FunSuite

import scala.language.implicitConversions

class DimacsSuite extends FunSuite {

  private implicit def stringToInputReader(value: String): Reader = new StringReader(value)

  test("Parsing dimacs with one clause and one variable") {
    val raw1 =
"""p cnf 1 1
1 0"""
    val (clauses1, nbVars1) = Dimacs.cnf(raw1)
    assert(nbVars1 === 1)
    assert(clauses1.size === 1 && clauses1.head.size === 1 && clauses1.head.head.polarity)
  }
}
