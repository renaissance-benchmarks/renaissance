//package regolic.sat
//
//import org.scalatest.FunSuite
//
//class NaiveSolverSuite extends FunSuite {
//
//  val l1 = new Literal(0, true)
//  val l2 = new Literal(0, false)
//  val l3 = new Literal(1, true)
//  val l4 = new Literal(1, false)
//  val l5 = new Literal(2, true)
//  val l6 = new Literal(2, false)
//
//  val c1 = Set(l1, l3, l5)
//  val c2 = Set(l2, l4, l6)
//  val c3 = Set(l1, l4)
//  val c4 = Set(l2, l5)
//  val c5 = Set(l2, l6)
//  val c6 = Set(l2, l3)
//  val c7 = Set(l1, l3)
//
//  test("isSat") {
//    assert(NaiveSolver.isSat(Set(c1, c2)) != None)
//    assert(NaiveSolver.isSat(Set(c3, c4)) != None)
//    assert(NaiveSolver.isSat(Set(c1, c3, c4)) != None)
//    assert(NaiveSolver.isSat(Set(c3, c4, c5)) != None)
//    assert(NaiveSolver.isSat(Set(c3, c4, c6)) != None)
//    assert(NaiveSolver.isSat(Set(c3, c4, c5, c7)) === None)
//  }
//
//  test("model is correct") {
//    val f1 = Set(c1, c2)
//    val m1 = NaiveSolver.isSat(f1)
//    m1.foreach(m => assert(Eval(f1, m)))
//
//    val f2 = Set(c3, c4, c6)
//    val m2 = NaiveSolver.isSat(f2)
//    m2.foreach(m => assert(Eval(f2, m)))
//  }
//
//}
