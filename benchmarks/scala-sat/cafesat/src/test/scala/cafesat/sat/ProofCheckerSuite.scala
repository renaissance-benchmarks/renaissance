package cafesat.sat

import org.scalatest.FunSuite

class ProofCheckerSuite extends FunSuite {

  private val a = new Literal(0, true)
  private val na = new Literal(0, false)
  private val b = new Literal(1, true)
  private val nb = new Literal(1, false)
  private val c = new Literal(2, true)
  private val nc = new Literal(2, false)
  private val emptyClause = Set[Literal]()

  test("Basic Proof") {
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
    assert(ProofChecker(proof.inferences, emptyClause))
  }

  test("Valid Proof") {
    val cl1 = Set(na, c)
    val cl2 = Set(a, b, c)
    val cl3 = Set(a, nb)
    val cl4 = Set(na, nc)
    val cl5 = Set(nc, b)

    val cl6 = Set(b, c)
    val cl7 = Set(a, c)
    val cl8 = Set(c)
    val cl9 = Set(b)
    val cl10 = Set(a)
    val cl11 = Set(nc)

    val proof = new Proof(Set(cl1, cl2, cl3, cl4, cl5))
    proof.infer(cl1, cl2, cl6)
    proof.infer(cl2, cl3, cl7)
    proof.infer(cl1, cl7, cl8)
    proof.infer(cl5, cl6, cl9)
    proof.infer(cl9, cl3, cl10)
    proof.infer(cl10, cl4, cl11)
    proof.infer(cl11, cl8, emptyClause)
    proof.linearize(emptyClause)
    assert(ProofChecker(proof.inferences, emptyClause))
  }

  test("Invalid Proof") {
    val cl1 = Set(na, c)
    val cl2 = Set(a, b, c)
    val cl3 = Set(a, nb)
    val cl4 = Set(na, nc)

    val cl6 = Set(b, c)
    val cl7 = Set(a, c)
    val cl8 = Set(c)
    val cl9 = Set(b)
    val cl10 = Set(a)
    val cl11 = Set(nc)

    val proof = new Proof(Set(cl1, cl2, cl3, cl4))
    proof.infer(cl1, cl2, cl6)
    proof.infer(cl2, cl3, cl7)
    proof.infer(cl1, cl7, cl8)
    proof.infer(cl4, cl6, cl9)
    proof.infer(cl9, cl3, cl10)
    proof.infer(cl10, cl4, cl11)
    proof.infer(cl11, cl8, emptyClause)
    proof.linearize(emptyClause)
    assert(!ProofChecker(proof.inferences, emptyClause))
  }

}
