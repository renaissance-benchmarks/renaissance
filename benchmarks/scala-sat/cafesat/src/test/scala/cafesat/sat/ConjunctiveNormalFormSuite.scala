//package regolic.sat
//
//import regolic.asts.fol.Trees._
//import regolic.asts.core.Trees._
//
//import org.scalatest.FunSuite
//
//class ConjunctiveNormalFormSuite extends FunSuite {
//
//  val q1 = freshPropositionalVariable("Q")
//  val q2 = freshPropositionalVariable("Q")
//  val q3 = freshPropositionalVariable("Q")
//  val r1 = freshPropositionalVariable("R")
//  val r2 = freshPropositionalVariable("R")
//
//  //def isEncodingSat(f: Formula): Boolean = {
//  //  val (cnf, nb, map) = ConjunctiveNormalForm(f)
//  //  val model = NaiveSolver.isSat(cnf)
//  //  model
//  //  if(isSat) {
//  //    if(model == Unsatisfiable) {
//  //      println(f + " was not encoded correctly")
//  //      println("encoding was: " + cnf)
//  //      println("with: " + map)
//  //      assert(false)
//  //    }
//  //  } else {
//  //    if(model.isInstanceOf[Satisfiable]) {
//  //      println(f + " was not encoded correctly")
//  //      println("encoding was: " + cnf)
//  //      println("with: " + map)
//  //      assert(false)
//  //    }
//  //  }
//  //}
//
//  test("cnf is equisat") {
//
//    val f1 = Or(And(q1,q2,q3), And(r1,r2))
//    val (cnf1, _, _) = ConjunctiveNormalForm(f1)
//    assert(NaiveSolver.isSat(cnf1) != None)
//
//    val f2 = And(Or(q1,q2,q3), Or(q1,Not(q2)), Or(q2, Not(q3)))
//    val (cnf2, _, _) = ConjunctiveNormalForm(f2)
//    assert(NaiveSolver.isSat(cnf2) != None)
//
//    val f3 = And(Or(Not(q1),q3), Or(q1,Not(q2)), Or(q2, Not(q3)), Or(q3, q2), Or(Not(q1), Not(q2)))
//    val (cnf3, _, _) = ConjunctiveNormalForm(f3)
//    assert(NaiveSolver.isSat(cnf3) === None)
//
//    val f4 = Implies(Or(Not(q1),q3), Or(q1,Not(q2)))
//    val (cnf4, _, _) = ConjunctiveNormalForm(f4)
//    assert(NaiveSolver.isSat(cnf4) != None)
//
//    val f5 = Iff(Or(Not(q1),q3), And(q1,Not(q2)))
//    val (cnf5, _, _) = ConjunctiveNormalForm(f5)
//    assert(NaiveSolver.isSat(cnf5) != None)
//
//    val f6 = Iff(q1, q2)
//    val (cnf6, _, _) = ConjunctiveNormalForm(f6)
//    assert(NaiveSolver.isSat(cnf6) != None)
//  }
//
//}
