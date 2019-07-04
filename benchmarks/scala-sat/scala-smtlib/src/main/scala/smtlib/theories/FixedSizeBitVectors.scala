package smtlib
package theories

import parser.Terms._
import common._

object FixedSizeBitVectors {


  object BitVectorSort {

    def apply(length: Int): Sort = {
      require(length > 0)
      Sort(Identifier(SSymbol("BitVec"), Seq(length)))
    }

    def unapply(sort: Sort): Option[Int] = sort match {
      case Sort(Identifier(SSymbol("BitVec"), Seq(n)), Seq()) if n > 0 => Some(n)
      case _ => None
    }

  }

  object BitVectorLit {

    def apply(content: List[Boolean]): Term = SBinary(content)

    def apply(content: Hexadecimal): Term = SHexadecimal(content)
    
    //TODO: going from List[Boolean] to Integer
    def unapply(term: Term): Option[List[Boolean]] = term match {
      case SBinary(content) => Some(content)
      case SHexadecimal(hexa) => Some(hexa.toBinary)
      case _ => None
    }

  }


  object Concat {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("concat"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("concat"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object Extract {

    def apply(i: Int, j: Int, t: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("extract"), Seq(i, j))),
        Seq(t)
      )
    
    def unapply(term: Term): Option[(Int, Int, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("extract"), Seq(i, j)),
          None
        ), Seq(t)) => Some((i, j, t))
      case _ => None
    }

  }

  object And {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvand"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvand"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object Or {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvor"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvor"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object Not {

    def apply(t: Term): Term = 
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("bvnot"))), Seq(t))
    
    def unapply(term: Term): Option[Term] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvnot"), Seq()),
          None
        ), Seq(t)) => Some(t)
      case _ => None
    }
  }

  object NAnd {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvnand"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvnand"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object NOr {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvnor"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvnor"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object XOr {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvxor"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvxor"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object XNOr {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvxnor"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvxnor"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object Comp {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvcomp"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvcomp"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object Neg {

    def apply(t: Term): Term = 
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol("bvneg"))), Seq(t))
    
    def unapply(term: Term): Option[Term] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvneg"), Seq()),
          None
        ), Seq(t)) => Some(t)
      case _ => None
    }
  }

  object Add {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvadd"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvadd"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object Sub {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvsub"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvsub"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }


  object Mul {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvmul"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvmul"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object UDiv {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvudiv"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvudiv"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object URem {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvurem"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvurem"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object ULessThan {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvult"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvult"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object ULessEquals {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvule"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvule"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object UGreaterThan {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvugt"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvugt"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object UGreaterEquals {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvuge"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvuge"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object SLessThan {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvslt"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvslt"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object SLessEquals {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvsle"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvsle"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object SGreaterThan {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvsgt"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvsgt"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }

  object SGreaterEquals {

    def apply(t1: Term, t2: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("bvsge"))),
        Seq(t1, t2)
      )
    
    def unapply(term: Term): Option[(Term, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("bvsge"), Seq()),
          None
        ), Seq(t1, t2)) => Some((t1, t2))
      case _ => None
    }

  }
      
}
