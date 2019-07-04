//package regolic
//package dpllt
//
//import scala.reflect._
//
///*
// * Combination of two theories. Assume the theories are disjoint.
// * Need to be careful, because shared variables among theories are not handled.
// */
//class BinaryTheory[T1 <: TheoryComponent, T2 <: TheoryComponent](val t1: T1, val t2: T2) extends TheoryComponent {
//
//  override val literalClassTag: ClassTag[Literal] = classTag[Lit]
//
//  type Literal = Lit
//  case class Lit(repr: Either[t1.Literal, t2.Literal]) extends AbstractLiteral {
//
//    override val id: Int = repr.fold(l1 => l1.id, l2 => l2.id)
//    override val polInt: Int = repr.fold(l1 => l1.polInt, l2 => l2.polInt)
//
//    //returns the positive literal (always true)
//    override def pos: Literal = Lit(repr.left.map(l1 => l1.pos).right.map(l2 => l2.pos))
//    //returns the negation of the literal
//    override def neg: Literal = Lit(repr.left.map(l1 => l1.neg).right.map(l2 => l2.neg))
//
//    override def toString: String = repr.fold(_.toString, _.toString)
//  }
//
//  type Solver = CombinedSolver
//
//  def makeSolver(cnf: Set[Set[Literal]]): Solver = {
//    val s1 = t1.makeSolver(cnf.map(clause => clause.flatMap{
//      case Lit(Left(t1Lit)) => List(t1Lit)
//      case _ => List()
//    }))
//    val s2 = t2.makeSolver(cnf.map(clause => clause.flatMap{
//      case Lit(Right(t2Lit)) => List(t2Lit)
//      case _ => List()
//    }))
//    new CombinedSolver(s1, s2)
//  }
//
//  class CombinedSolver(val s1: t1.Solver, val s2: t2.Solver) extends AbstractSolver {
//
//    private val iStack = new scala.collection.mutable.Stack[Literal]
//
//    override def isTrue(l: Literal): Boolean = l match {
//      case Lit(Left(t1Lit)) => s1.isTrue(t1Lit)
//      case Lit(Right(t2Lit)) => s2.isTrue(t2Lit)
//    }
//
//    override def backtrack(n: Int): Unit = {
//      for(i <- 0 until n) {
//        iStack.pop match {
//          case Lit(Left(_)) => s1.backtrack(1)
//          case Lit(Right(_)) => s2.backtrack(1)
//        }
//      }
//    }
//
//    //TODO
//    override def check(): Option[Set[Literal]] = ???
//
//    override def setTrue(l: Literal): Either[Set[Literal], Set[Literal]] = {
//      iStack.push(l)
//      l match {
//        case Lit(Left(t1Lit)) => 
//          s1.setTrue(t1Lit)
//          .left.map(_.map(l => Lit(Left(l))))
//          .right.map(_.map((l => Lit(Left(l)))))
//        case Lit(Right(t2Lit)) => 
//          s2.setTrue(t2Lit)
//          .left.map(_.map(l => Lit(Right(l))))
//          .right.map(_.map(l => Lit(Right(l))))
//      }
//    }
//
//    override def explanation(l: Literal): Set[Literal] = l match {
//      case Lit(Left(t1Lit)) => s1.explanation(t1Lit).map(l => Lit(Left(l)))
//      case Lit(Right(t2Lit)) => s2.explanation(t2Lit).map(l => Lit(Right(l)))
//    }
//
//  }
//
//}
