package smtlib
package theories

import trees.Terms._
import common._

import Operations._

object FixedSizeBitVectors {

  object BitVectorSort {
    def apply(length: BigInt): Sort = {
      require(length > 0)
      Sort(Identifier(SSymbol("BitVec"), Seq(SNumeral(length))))
    }
    def unapply(sort: Sort): Option[BigInt] = sort match {
      case Sort(Identifier(SSymbol("BitVec"), Seq(SNumeral(n))), Seq()) if n > 0 => Some(n)
      case _ => None
    }
  }

  object BitVectorLit {
    def apply(content: List[Boolean]): Term = SBinary(content)

    /** Construct a bit-vector literal from an hexadecimal
      *
      * The bitvector theory interprets the hexadecimal literals
      * as a bit vector of size 4 times the length of the hexadecimal
      * representation
      */
    def apply(content: Hexadecimal): Term = SHexadecimal(content)

    def unapply(term: Term): Option[List[Boolean]] = term match {
      case SBinary(content) => Some(content)
      case SHexadecimal(hexa) => Some(hexa.toBinary)
      case _ => None
    }
  }

  /**
    * shorthand notation (_ bv13 32) for the number 13 with 32 bits
    */
  object BitVectorConstant {
    def apply(x: BigInt, n: BigInt): Term =
      QualifiedIdentifier(Identifier(SSymbol("bv" + x), Seq(SNumeral(n))))
    //TODO: BigInt is not the best data representation for a bitvector, we should probably use a list of boolean kind of representation
    def unapply(term: Term): Option[(BigInt, BigInt)] = term match {
      case QualifiedIdentifier(
        Identifier(SSymbol(cst), Seq(SNumeral(size))),
        None
      ) if cst startsWith "bv" =>
        Some(BigInt(cst drop 2) -> size)

      case _ => None
    }
  }


  object Concat extends Operation2 { override val name = "concat" }

  object Not extends Operation1 { override val name = "bvnot" }
  object Neg extends Operation1 { override val name = "bvneg" }
  object And extends Operation2 { override val name = "bvand" }
  object Or extends Operation2 { override val name = "bvor" }
  object NAnd extends Operation2 { override val name = "bvnand" }
  object NOr extends Operation2 { override val name = "bvnor" }
  object XOr extends Operation2 { override val name = "bvxor" }
  object XNOr extends Operation2 { override val name = "bvxnor" }

  object Comp extends Operation2 { override val name = "bvcomp" }
  object Add extends Operation2 { override val name = "bvadd" }
  object Sub extends Operation2 { override val name = "bvsub" }
  object Mul extends Operation2 { override val name = "bvmul" }
  object UDiv extends Operation2 { override val name = "bvudiv" }
  object SDiv extends Operation2 { override val name = "bvsdiv" }
  object URem extends Operation2 { override val name = "bvurem" }
  object SRem extends Operation2 { override val name = "bvsrem" }
  object SMod extends Operation2 { override val name = "bvsmod" }

  object ULessThan extends Operation2 { override val name = "bvult" }
  object ULessEquals extends Operation2 { override val name = "bvule" }
  object UGreaterThan extends Operation2 { override val name = "bvugt" }
  object UGreaterEquals extends Operation2 { override val name = "bvuge" }
  object SLessThan extends Operation2 { override val name = "bvslt" }
  object SLessEquals extends Operation2 { override val name = "bvsle" }
  object SGreaterThan extends Operation2 { override val name = "bvsgt" }
  object SGreaterEquals extends Operation2 { override val name = "bvsge" }

  object ShiftLeft extends Operation2 { override val name = "bvshl" }
  object LShiftRight extends Operation2 { override val name = "bvlshr" }
  object AShiftRight extends Operation2 { override val name = "bvashr" }


  object Extract {
    def apply(i: BigInt, j: BigInt, t: Term): Term =
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("extract"), Seq(SNumeral(i), SNumeral(j)))),
        Seq(t)
      )
    def unapply(term: Term): Option[(BigInt, BigInt, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("extract"), Seq(SNumeral(i), SNumeral(j))),
          None
        ), Seq(t)) => Some((i, j, t))
      case _ => None
    }
  }

  object Repeat {
    def apply(i: BigInt, t: Term): Term = {
      require(i >= 1)
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("repeat"), Seq(SNumeral(i)))),
        Seq(t)
      )
    }
    def unapply(term: Term): Option[(BigInt, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("repeat"), Seq(SNumeral(i))),
          None
        ), Seq(t)) => Some((i, t))
      case _ => None
    }
  }

  object ZeroExtend {
    def apply(i: BigInt, t: Term): Term = {
      require(i >= 0)
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("zero_extend"), Seq(SNumeral(i)))),
        Seq(t)
      )
    }
    def unapply(term: Term): Option[(BigInt, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("zero_extend"), Seq(SNumeral(i))),
          None
        ), Seq(t)) => Some((i, t))
      case _ => None
    }
  }

  object SignExtend {
    def apply(i: BigInt, t: Term): Term = {
      require(i >= 0)
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("sign_extend"), Seq(SNumeral(i)))),
        Seq(t)
      )
    }
    def unapply(term: Term): Option[(BigInt, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("sign_extend"), Seq(SNumeral(i))),
          None
        ), Seq(t)) => Some((i, t))
      case _ => None
    }
  }

  object RotateLeft {
    def apply(i: BigInt, t: Term): Term = {
      require(i >= 0)
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("rotate_left"), Seq(SNumeral(i)))),
        Seq(t)
      )
    }
    def unapply(term: Term): Option[(BigInt, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("rotate_left"), Seq(SNumeral(i))),
          None
        ), Seq(t)) => Some((i, t))
      case _ => None
    }
  }

  object RotateRight {
    def apply(i: BigInt, t: Term): Term = {
      require(i >= 0)
      FunctionApplication(
        QualifiedIdentifier(Identifier(SSymbol("rotate_right"), Seq(SNumeral(i)))),
        Seq(t)
      )
    }
    def unapply(term: Term): Option[(BigInt, Term)] = term match {
      case FunctionApplication(
        QualifiedIdentifier(
          Identifier(SSymbol("rotate_right"), Seq(SNumeral(i))),
          None
        ), Seq(t)) => Some((i, t))
      case _ => None
    }
  }

}
