package cafesat.sat

import org.scalatest.FunSuite

class InterpolationSuite extends FunSuite {

  private val a = new Literal(0, true)
  private val na = new Literal(0, false)
  private val b = new Literal(1, true)
  private val nb = new Literal(1, false)
  private val c = new Literal(2, true)
  private val nc = new Literal(2, false)
  private val emptyClause = Set[Literal]()

  test("Basic Interpolant") {
    {
      val cl1 = Set(na)
      val cl2 = Set(a, b)
      val cl3 = Set(a, nb)

      val cl4 = Set(b)
      val cl5 = Set(nb)

      val proof = new Proof(Set(cl1, cl2, cl3))
      proof.infer(cl1, cl2, cl4)
      proof.infer(cl1, cl3, cl5)
      proof.infer(cl4, cl5, emptyClause)
      proof.linearize(emptyClause)

      println(Interpolation(proof, Set(cl2, cl3), Set(cl1))) //should be a
      println(Interpolation(proof, Set(cl1), Set(cl2, cl3))) //should be Not(a)
    }

    {
      val cl1 = Set(a, b)
      val cl2 = Set(na, c)
      val cl3 = Set(nb, c)
      val cl4 = Set(nc)

      val cl5 = Set(b, c)
      val cl6 = Set(c)

      val proof = new Proof(Set(cl1, cl2, cl3, cl4))
      proof.infer(cl1, cl2, cl5)
      proof.infer(cl5, cl3, cl6)
      proof.infer(cl6, cl4, emptyClause)
      proof.linearize(emptyClause)
      println(Interpolation(proof, Set(cl1, cl3), Set(cl2, cl4))) // should be Or(a, c)
    }
  }
}
