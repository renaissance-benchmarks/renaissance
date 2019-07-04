//package regolic
//package dpllt
//
//import regolic.asts.core.Trees._
//import regolic.asts.fol.Trees._
//
//import scala.collection.mutable.ArrayBuffer
//import scala.collection.mutable.HashMap
//import scala.collection.mutable.ListBuffer
//
//class PropositionalSkeleton[T <: TheoryComponent](val theory: T) {
//
//  import theory.Literal
//
//  def apply(formula: Formula, makePropVar: (Int, Boolean) => Literal, builder: (PredicateApplication, Int, Boolean) => Literal): 
//    (Set[Set[Literal]], Int, Map[Formula, Literal]) = {
//
//    //TODO: move in some util/common generics class
//    trait Counter {
//      private var counter = -1
//      def next = {
//        counter += 1
//        counter
//      }
//
//      def count = counter + 1
//
//      def reset = {
//        counter = -1
//      }
//    }
//    object LiteralId extends Counter
//
//    val constraints = new ListBuffer[Set[Literal]]
//    var varToLiteral = new HashMap[Formula, Literal]()
//
//    //for each subformula, create a new representation and add the constraints while returning the representation
//    //the representative is a literal (positive or negative) that is equivalent to the formula
//    def rec(form: Formula): Literal = form match {
//      case p@Equals(_, _) => varToLiteral.get(p) match {
//        case Some(repr) => repr
//        case None => {
//          val repr = builder(p, LiteralId.next, true)
//          varToLiteral(p) = repr
//          repr
//        }
//      }
//      case p@Not(eq@Equals(_, _)) => varToLiteral.get(eq) match {
//        case Some(repr) => repr.neg
//        case None => {
//          val repr = builder(eq, LiteralId.next, true)
//          varToLiteral(eq) = repr
//          repr.neg
//        }
//      }
//      case p@PropositionalVariable(_) => varToLiteral.get(p) match {
//        case Some(repr) => repr
//        case None => {
//          //val repr = new PropositionalLiteral(LiteralId.next, true)
//          val repr = makePropVar(LiteralId.next, true)
//          varToLiteral(p) = repr
//          repr
//        }
//      }
//      case Not(f) => {
//        val fRepr = rec(f)
//        //val repr = new PropositionalLiteral(LiteralId.next, true)
//        val repr = makePropVar(LiteralId.next, true)
//        constraints += Set(repr.neg, fRepr.neg)
//        constraints += Set(repr.pos, fRepr)
//        repr
//      }
//      case And(fs) => {
//        //val repr = new PropositionalLiteral(LiteralId.next, true)
//        val repr = makePropVar(LiteralId.next, true)
//        val fsRepr = fs.map(f => rec(f))
//        for(fRepr <- fsRepr)
//          constraints += Set(repr.neg, fRepr)
//        constraints += (repr :: fsRepr.map(fRepr => fRepr.neg)).toSet
//        repr
//      }
//      case Or(fs) => {
//        //val repr = new PropositionalLiteral(LiteralId.next, true)
//        val repr = makePropVar(LiteralId.next, true)
//        val fsRepr = fs.map(f => rec(f))
//        for(fRepr <- fsRepr)
//          constraints += Set(repr, fRepr.neg)
//        constraints += (repr.neg :: fsRepr).toSet
//        repr
//      }
//      case Implies(f1, f2) => {
//        //val repr = new PropositionalLiteral(LiteralId.next, true)
//        val repr = makePropVar(LiteralId.next, true)
//        val f1Repr = rec(f1)
//        val f2Repr = rec(f2)
//        constraints += Set(repr.neg, f1Repr.neg, f2Repr)
//        constraints += Set(repr, f1Repr)
//        constraints += Set(repr, f2Repr.neg)
//        repr
//      }
//      case Iff(f1, f2) => {
//        //val repr = new PropositionalLiteral(LiteralId.next, true)
//        val repr = makePropVar(LiteralId.next, true)
//        val f1Repr = rec(f1)
//        val f2Repr = rec(f2)
//        constraints += Set(repr.neg, f1Repr.neg, f2Repr)
//        constraints += Set(repr.neg, f1Repr, f2Repr.neg)
//        constraints += Set(repr, f1Repr.neg, f2Repr.neg)
//        constraints += Set(repr, f1Repr, f2Repr)
//        repr
//      }
//      case _ => sys.error("Unhandled case in ConjunctiveNormalForm: " + form)
//    }
//
//    val repr = rec(formula)
//    constraints += Set(repr)
//     
//    (constraints.toSet, LiteralId.count, varToLiteral.toMap)
//  }
//
//}
