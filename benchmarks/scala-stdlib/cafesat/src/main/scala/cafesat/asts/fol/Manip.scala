package cafesat
package asts
package fol

import Trees._
import common.Math.fix
import core.Manip._
import core.Trees._

object Manip {

  def simplify(formula: Formula): Formula = {
    def simplifyOne(f: Formula): Formula = {
      def simplifyOneNot(f: Formula): Formula = f match {
        case Not(Not(f)) => f
        case Not(True()) => False()
        case Not(False()) => True()
        case f@_ => f match {
          case Not(And(fs)) => {
            val nbn = fs.count(isNot)
            val nbr = fs.length - nbn
            if(nbn >= nbr)
              Or(fs.map{ case Not(f) => f case f@_ => Not(f) })
            else
              f
          }
          case Not(Or(fs)) => {
            val nbn = fs.count(isNot)
            val nbr = fs.length - nbn
            if(nbn >= nbr)
              And(fs.map{ case Not(f) => f case f@_ => Not(f) })
            else
              f
          }
          case _ => f
        }
      }
      def simplifyOneAnd(f: Formula): Formula = f match {
        case And(Nil) => True()
        case And(f :: Nil) => f
        case And(fs) if fs.exists(isFalse) => False()
        case And(fs) if fs.exists(isTrue) => And(fs.filterNot(isTrue))
        case And(fs) => {
          val nfs = fs.flatMap({ case And(fs2) => fs2 case f2 => List(f2)})
          val nbn = nfs.count(isNot)
          val nbr = nfs.length - nbn
          if(nbn > nbr + 1)
            Not(Or(nfs.map{ case Not(f) => f case f@_ => Not(f) }))
          else
            And(nfs)
        }
        case f@_ => f
      }
      def simplifyOneOr(f: Formula): Formula = f match {
        case Or(Nil) => False()
        case Or(f :: Nil) => f
        case Or(f1 :: Not(f2) :: Nil) =>  Implies(f2, f1)
        case Or(Not(f1) :: f2 :: Nil) =>  Implies(f1, f2)
        case Or(fs) if fs.exists(isTrue) => True()
        case Or(fs) if fs.exists(isFalse) => Or(fs.filterNot(isFalse))
        case Or(fs) => {
          val nfs = fs.flatMap({ case Or(fs2) => fs2 case f2 => List(f2)})
          val nbn = nfs.count(isNot)
          val nbr = nfs.length - nbn
          if(nbn > nbr + 1)
            Not(And(nfs.map{ case Not(f) => f case f@_ => Not(f) }))
          else
            Or(nfs)
        }
        case f@_ => f
      }
      def simplifyOneIfThenElse(f: Formula): Formula = f match {
        case IfThenElse(True(), f, _) => f
        case IfThenElse(False(), _, f) => f
        case IfThenElse(_, True(), True()) => True()
        case IfThenElse(_, False(), False()) => False()
        case f@_ => f
      }
      def simplifyOneImplies(f: Formula): Formula = f match {
        case Implies(False(), _) => True()
        case Implies(_, True()) => True()
        case Implies(f, False()) => Not(f)
        case Implies(True(), f) => f
        case Implies(Not(f1), f2) => Or(List(f1, f2))
        case f@_ => f
      }
      def simplifyOneIff(f: Formula): Formula = f match {
        case Iff(False(), True()) => False()
        case Iff(False(), False()) => True()
        case Iff(False(), f) => Not(f)
        case Iff(True(), True()) => True()
        case Iff(True(), False()) => False()
        case Iff(True(), f) => f
        case Iff(f, False()) => Not(f)
        case Iff(f, True()) => f
        case f@_ => f
      }

      f match {
        case Not(_) => simplifyOneNot(f)
        case And(_) => simplifyOneAnd(f)
        case Or(_) => simplifyOneOr(f)
        case Implies(_,_) => simplifyOneImplies(f)
        case Iff(_,_) => simplifyOneIff(f)
        case IfThenElse(_,_,_) => simplifyOneIfThenElse(f)
        case f@_ => f
      }
    }

    def mapSimplify(f: Formula): Formula = mapPostorder(f, simplifyOne, x => x)

    fix(mapSimplify,formula)
  }

  //a conjunctive normal form, always as an And of Ors (even with single formula)
  //literals are either predicate, negation of predicate or true/false
  def isConjunctiveNormalForm(formula: Formula): Boolean = formula match {
    case And(fs) => fs.forall{
      case Or(fs2) => fs2.forall(f => f match {
        case True() | False() => true
        case Not(PredicateApplication(_, _)) => true
        case PredicateApplication(_, _) => true
        case _ => false
      })
      case _ => false
    }
    case _ => false
  }
  def conjunctiveNormalForm(formula: Formula): Formula = {
    require(isQuantifierFree(formula))

    def distribute(and1: Formula, and2: Formula): Formula = {
      val (And(fs1), And(fs2)) = (and1, and2)
      And(fs1.flatMap{ case Or(fss1) =>
        fs2.map{ case Or(fss2) => Or(fss1 ::: fss2) }
      })
    }

    def inductiveStep(f: Formula): Formula = f match {
      case And(fs) => fs match {
        case Nil => And(List(Or(List())))
        case fs => And(fs.flatMap{ case And(fs2) => fs2 })
      }
      case Or(fs) => fs match {
        case Nil => And(List(Or(List())))
        case f::Nil => f
        case fs => And(
          fs.reduceLeft((and1, and2) => distribute(and1, and2)) match {
            case And(fs2) => fs2
          }
        )
      }
      case Not(And(fs)) => inductiveStep(Or(fs.map{
        case Or(fs2) => And(fs2.map{ //I map to an Or so that each element is in cnf
          case Not(f) => Or(List(f))
          case f => Or(List(Not(f)))
        })
      }))

      case PredicateApplication(_, _) | True() | False() => And(List(Or(List(f))))

      case _ => sys.error("unexpected formula: " + f)

    }

    cleanTrueFalseCNF(mapPostorder(basicForm(formula), inductiveStep, t => t))
  }
  //this transformation generate a much smaller formula, but the formula is only equisatisfiable to the original one
  def conjunctiveNormalFormEquisat(formula: Formula): Formula = {
    import scala.collection.mutable.HashMap
    import scala.collection.mutable.ListBuffer

    val representations = new HashMap[Formula, PredicateApplication]
    val constraints = new ListBuffer[Formula]

    //for each subformula, create a new representation and add the constraints while returning the representation
    def inductionStep(subForm: Formula): Formula = subForm match {
      case Not(f) => {
        val repr = freshPropositionalVariable("P")
        constraints += Or(Not(repr), Not(f))
        constraints += Or(repr, f)
        repr
      }
      case And(fs) => {
        val repr = freshPropositionalVariable("P")
        for(f <- fs)
          constraints += Or(Not(repr), f)
        constraints += Or(repr :: fs.map(Not(_)))
        repr
      }
      case Or(fs) => {
        val repr = freshPropositionalVariable("P")
        constraints += Or(Not(repr) :: fs)
        for(f <- fs)
          constraints += Or(repr, Not(f))
        repr
      }
      case Implies(f1, f2) => {
        val repr = freshPropositionalVariable("P")
        constraints += Or(Not(repr), Not(f1), f2)
        constraints += Or(repr, f1)
        constraints += Or(repr, Not(f2))
        repr
      }
      case Iff(f1, f2) => {
        val repr = freshPropositionalVariable("P")
        constraints += Or(Not(repr), Not(f1), f2)
        constraints += Or(Not(repr), f1, Not(f2))
        constraints += Or(repr, Not(f1), Not(f2))
        constraints += Or(repr, f1, f2)
        repr
      }
      case _ => subForm
    }

    val repr = mapPostorder(formula, inductionStep _, (t: Term) => t)
    constraints += repr
     
    cleanTrueFalseCNF(And(constraints.toList))
  }

  private def cleanTrueFalseCNF(and: Formula): Formula = {
    val And(ors) = and
    var falseOccurs = false
    val newOrs = ors.flatMap(or => {
      val Or(lits) = or
      var trueOccurs = false
      val newLits = lits.flatMap{
        case False() | Not(True()) => Nil
        case True() | Not(False()) => trueOccurs = true; Nil
        case lit => List(lit)
      }
      if(trueOccurs) Nil 
      else if(newLits == Nil) { falseOccurs = true; Nil }
      else List(Or(newLits))
    })
    if(falseOccurs) And(Or(False())) 
    else if(newOrs == Nil) And(Or(True()))
    else And(newOrs)
  }

  //a disjunctive normal form, always as an Or of Ands (even with single formula)
  def isDisjunctiveNormalForm(formula: Formula): Boolean = formula match {
    case Or(fs) => fs.forall{
      case And(fs2) => fs2.forall(f => f match {
        case True() | False() => true
        case Not(PredicateApplication(_, _)) => true
        case PredicateApplication(_, _) => true
        case _ => false
      })
      case _ => false
    }
    case _ => false
  }
  def disjunctiveNormalForm(formula: Formula): Formula = {
    require(isQuantifierFree(formula))

    def distribute(or1: Formula, or2: Formula): Formula = {
      val (Or(fs1), Or(fs2)) = (or1, or2)
      Or(fs1.flatMap{ case And(fss1) =>
        fs2.map{ case And(fss2) => And(fss1 ::: fss2) }
      })
    }

    def cleanTrueFalse(or: Formula): Formula = {
      val Or(ands) = or
      var trueOccurs = false
      val newAnds = ands.flatMap(and => {
        val And(lits) = and
        var falseOccurs = false
        val newLits = lits.flatMap{
          case True() | Not(False()) => Nil
          case False() | Not(True()) => falseOccurs = true; Nil
          case lit => List(lit)
        }
        if(falseOccurs) Nil 
        else if(newLits == Nil) { trueOccurs = true; Nil }
        else List(And(newLits))
      })
      if(trueOccurs) Or(And(True())) 
      else if(newAnds == Nil) Or(And(False()))
      else Or(newAnds)
    }

    def inductiveStep(f: Formula): Formula = f match {
      case Or(fs) => fs match {
        case Nil => Or(List(And(List())))
        case fs => Or(fs.flatMap{ case Or(fs2) => fs2 })
      }
      case And(fs) => fs match {
        case Nil => Or(List(And(List())))
        case f::Nil => f
        case fs => Or(
          fs.reduceLeft((or1, or2) => distribute(or1, or2)) match {
            case Or(fs2) => fs2
          }
        )
      }
      case Not(Or(fs)) => inductiveStep(And(fs.map{
        case And(fs2) => Or(fs2.map{
          case Not(f) => And(List(f))
          case f => And(List(Not(f)))
        })
      }))

      case PredicateApplication(_, _) | True() | False()  => Or(List(And(List(f))))

      case _ => sys.error("unexpected formula: " + f)

    }

    cleanTrueFalse(mapPostorder(basicForm(formula), inductiveStep, t => t))
  }

  //basic form is form containing only quantifiers with And, Or and Not connectives
  def isBasicForm(formula: Formula): Boolean = forall(formula, (f: Formula) => f match {
    case Iff(_, _) | Implies(_, _) | IfThenElse(_, _, _) => false
    case _ => true
  })
  def basicForm(formula: Formula): Formula = {
    def inductiveStep(f: Formula): Formula = f match {
      case Iff(f1, f2) => Or(List(And(List(f1, f2)), And(List(Not(f1), Not(f2)))))
      case Implies(f1, f2) => Or(List(f2, Not(f1)))
      case IfThenElse(f1, f2, f3) => And(List(Or(List(Not(f1), f2)), Or(List(f1, f3)))) //TODO: I'm not so sure about the meaning of IfThenElse
      case _ => f
    }

    mapPostorder(formula, inductiveStep, t => t)
  }

  //negation normal form (nnf) only contains quantifier, NOT, AND and OR connectives (basic form) and 
  //NOT only appears above a predicate 
  def isNegationNormalForm(formula: Formula): Boolean = forall(formula, (f: Formula) => f match {
    case Not(f2) => f2.isInstanceOf[PredicateApplication]
    case Iff(_, _) | Implies(_, _) | IfThenElse(_, _, _) => false
    case _ => true
  })

  def negationNormalForm(formula: Formula): Formula = {
    def inductiveStep(f: Formula): Formula = f match {
      case Not(And(fs)) => Or(fs.map(f => Not(f)))
      case Not(Or(fs)) => And(fs.map(f => Not(f)))
      case Not(Forall(x, f)) => Exists(x, Not(f))
      case Not(Exists(x, f)) => Forall(x, Not(f))
      case Not(Not(f)) => f
      case Not(True()) => False()
      case Not(False()) => True()
      case _ => f
    }

    mapPreorder(basicForm(formula), inductiveStep, t => t)
  }


  //prenex form is with all quantifier at the top level and a quantifier free function inside
  def isPrenexNormalForm(formula: Formula): Boolean = formula match {
    case Forall(_, f) => isPrenexNormalForm(f)
    case Exists(_, f) => isPrenexNormalForm(f)
	  case _ => forall(formula, (f: Formula) => f match {
      case Forall(_, _) | Exists(_, _) => false
      case _ => true
    })
  }

  def prenexNormalForm(formula: Formula): Formula = {
    def oneStep(f: Formula): Formula = f match {
      case Or(fs) => {
        var quants: List[(Boolean, Variable)] = List()
        val newFs = fs.map{
          case Forall(x, b) => {
            quants ::= (true, x)
            b
          }
          case Exists(x, b) => {
            quants ::= (false, x)
            b
          }
          case f => f
        }
        quants.foldLeft(Or(newFs): Formula)((a, q) => if(q._1) Forall(q._2, a) else Exists(q._2, a))
      }
      case And(fs) => {
        var quants: List[(Boolean, Variable)] = List()
        val newFs = fs.map{
          case Forall(x, b) => {
            quants ::= (true, x)
            b
          }
          case Exists(x, b) => {
            quants ::= (false, x)
            b
          }
          case f => f
        }
        quants.foldLeft(And(newFs): Formula)((a, q) => if(q._1) Forall(q._2, a) else Exists(q._2, a))
      }
      case Not(Forall(x, b)) => Exists(x, Not(b))
      case Not(Exists(x, b)) => Forall(x, Not(b))
      case Implies(Forall(x, b), f) => Exists(x, Implies(b, f))
      case Implies(Exists(x, b), f) => Forall(x, Implies(b, f))
      case Implies(f, Forall(x, b)) => Forall(x, Implies(f, b))
      case Implies(f, Exists(x, b)) => Exists(x, Implies(f, b))
      case Iff(_, _) => sys.error("TODO")
      case IfThenElse(_, _, _) => sys.error("TODO")
      case f => f
    }
    def rec(f: Formula): Formula = mapPostorder(f, oneStep, t => t)

    val cleanFormula = alphaRenaming(formula)
    fix(rec, cleanFormula)
  }


  //prenex normal form and only universal quantifier: \forall x1, x2, ... F, where F is quant. free
  def isSkolemNormalForm(formula: Formula): Boolean = formula match {
    case Forall(_, f) => isPrenexNormalForm(f)
	  case _ => forall(formula, (f: Formula) => f match {
      case Forall(_, _) | Exists(_, _) => false
      case _ => true
    })
  }

  //skolemization only maintains equisatisfiability, not equivalence.
  def skolemNormalForm(formula: Formula): Formula = {
    def rec(formula: Formula, scope: List[Variable]): Formula = formula match {
      case Exists(v, rest) => {
        val skolemFunction = freshFunctionSymbol("f", scope.map(_.sort), v.sort)
        val skolemTerm = FunctionApplication(skolemFunction, scope)
        val freshRest = substitute(rest, v, skolemTerm)
        rec(freshRest, scope)
      }
      case Forall(v, rest) => Forall(v, rec(rest, v :: scope))
      case f => f
    }
    val prenexFormula = prenexNormalForm(formula)
    rec(prenexFormula, Nil)
  }

  def clausalNormalForm(formula: Formula): Formula = {
    def dropQuant(f: Formula): Formula = f match {
      case Forall(x, f) => dropQuant(f)
      case _ => f
    }

    val skolemForm = skolemNormalForm(formula)
    val body = dropQuant(skolemForm)
    val cnf = conjunctiveNormalForm(body) //This should be ok to use the equisat version without exponential blowup
    cnf
  }

  def isQuantifierFree(f: Formula): Boolean = forall(f, (sf: Formula) => sf match {
    case Forall(_, _) | Exists(_, _) => false
    case _ => true
  })


  def substitutePropVar(f: Formula, m: Map[PredicateApplication, Formula]): Formula = mapPostorder(f, {
    case p2@PropositionalVariable(_) => m.get(p2) match {
      case Some(nf) => nf
      case None => p2
    }
    case f@_ => f
  }, t => t)
  def substitutePropVar(f: Formula, p: PredicateApplication, newF: Formula): Formula = substitutePropVar(f, Map(p -> newF))

  def substituteConst(f: Formula, m: Map[FunctionApplication, Term]): Formula = mapPostorder(f, f => f, {
    case c2@Constant(_, _) => m.get(c2) match {
      case Some(nt) => nt
      case None => c2
    }
    case t@_ => t
  })
  def substituteConst(f: Formula, fun: FunctionApplication, nt: Term): Formula = substituteConst(f, Map(fun -> nt))
  def substituteConst(t: Term, m: Map[FunctionApplication, Term]): Term = mapPostorder(t, f => f, {
    case c2@Constant(_, _) => m.get(c2) match {
      case Some(nt) => nt
      case None => c2
    }
    case t@_ => t
  })
  def substituteConst(t: Term, fun: FunctionApplication, nt: Term): Term = substituteConst(t, Map(fun -> nt))

  def propVars(t: Term): Set[PredicateApplication] = foldPostorder(t, Set[PredicateApplication]())((a, f) => f match {
      case v@PropositionalVariable(_) => a + v
      case _ => a
    }, (a, t) => a)
  def propVars(f: Formula): Set[PredicateApplication] = foldPostorder(f, Set[PredicateApplication]())((a, f) => f match {
      case v@PropositionalVariable(_) => a + v
      case _ => a
    }, (a, t) => a)
  def consts(t: Term): Set[FunctionApplication] = foldPostorder(t, Set[FunctionApplication]())((a, f) => a, (a, t) => t match {
      case c@Constant(_, _) => a + c
      case _ => a
    })
  def consts(f: Formula): Set[FunctionApplication] = foldPostorder(f, Set[FunctionApplication]())((a, f) => a, (a, t) => t match {
      case c@Constant(_, _) => a + c
      case _ => a
    })



  private def isTrue(f: Formula) = f match {
    case True() => true
    case _ => false
  }
  private def isFalse(f: Formula) = f match {
    case False() => true
    case _ => false
  }
  private def isNot(f: Formula) = f match {
    case Not(_) => true
    case _ => false
  }
  private def isQuantifier(f: Formula) = f match {
    case Forall(_, _) | Exists(_, _) => true
    case _ => false
  }
}
