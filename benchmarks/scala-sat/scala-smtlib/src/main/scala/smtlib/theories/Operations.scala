package smtlib
package theories

import trees.Terms._

/** General patterns for building and extracting FunctionApplication in theories.
  *
  * Most SMT-LIB theories are a definition of many built-in functions. We do not
  * wish to extend the core abstract syntax tree of SMT-LIB with theory specific
  * operations, so a theory definition is simply providing Constructors and Extractors
  * to build the proper trees out of core SMT-LIB FunctionApplication and Identifier.
  *
  * this object provides traits to facilitate the definition of custom 
  * FunctionApplication with apply and unapply methods. They provide the proper 
  * signatures for different arities.
  *
  * Refer to any theory definition to see examples of how to use these traits.
  */
object Operations {

  /**
   * Operations with no arguments
   */
  trait Operation0 {
    val name: String

    def apply(): Term = QualifiedIdentifier(Identifier(SSymbol(name)))

    def unapply(t : Term): Boolean = t match {
      case QualifiedIdentifier(Identifier(SSymbol(`name`), Seq()), None) => true
      case _ => false
    }
  }

  /**
   * Operations with exactly one argument
   */
  trait Operation1 {
    val name: String

    def apply(i : Term): Term =
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))),
                            Seq(i))

    def unapply(t : Term): Option[Term] = t match {
      case FunctionApplication(
            QualifiedIdentifier(Identifier(SSymbol(`name`), Seq()), None),
            Seq(i)) => Some(i)
      case _ => None
    }
  }

  /**
   * Operations with exactly two argument
   */
  trait Operation2 {
    val name: String

    def apply(l : Term, r : Term): Term =
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))),
                            Seq(l,r))

    def unapply(t : Term): Option[(Term, Term)] = t match {
      case FunctionApplication(
            QualifiedIdentifier(Identifier(SSymbol(`name`), Seq()), None),
            Seq(l,r)) => Some((l,r))
      case _ => None
    }
  }

  /**
   * Operations with exactly three argument
   */
  trait Operation3 {
    val name: String

    def apply(l : Term, m : Term, r : Term): Term =
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))),
                            Seq(l,m,r))

    def unapply(t : Term): Option[(Term, Term, Term)] = t match {
      case FunctionApplication(
            QualifiedIdentifier(Identifier(SSymbol(`name`), Seq()), None),
            Seq(l,m,r)) => Some((l,m,r))
      case _ => None
    }
  }

  /**
   * Operations with variable number of arguments, requiring that the number of arguments is greater than least `numRequired`
   */
  trait OperationN {
    val name: String

    val numRequired: Int

    def apply(is: Seq[Term]): Term = {
      require(is.size >= numRequired)
      FunctionApplication(QualifiedIdentifier(Identifier(SSymbol(name))), is)
    }

    //TODO: not sure which unapply is better to provide
    //def unapply(t : Term): Option[Seq[Term]] = t match {
    //  case FunctionApplication(
    //        QualifiedIdentifier(Identifier(SSymbol(`name`), Seq()), None),
    //        is) if is.size >= numRequired => Some(is)
    //  case _ => None
    //}

    def unapplySeq(term: Term): Option[Seq[Term]] = term match {    
      case FunctionApplication(   
        QualifiedIdentifier(   
          Identifier(SSymbol(`name`), Seq()),
          None
        ), seqTerm) if seqTerm.length >= 2 => Some(seqTerm)
      case _ => None   
    }

  }

  /**
   * Operations with variable number of arguments, none required
   */
  trait OperationN0 extends OperationN {
    override val numRequired: Int = 0
  }

  /**
   * Operations with variable number of arguments, at least one required
   */
  trait OperationN1 extends OperationN {
    override val numRequired: Int = 1

    def apply(i1: Term, is: Term*): Term = apply(i1 +: is)
  }

  /** Operations with variable number of arguments, at least two required
    *
    * Corresponds to the many operations that are defined for two arguments and
    * marked as :left-assoc or :pairwise (such as `and` or `distinct`). Note that
    * the resulting representation in terms of AST will be the n-ary function application,
    * and not the desugared version (successive binary operation). This choice seems to
    * make sense for operations such as distinct that would require an exponential
    * blowup to desugar the expression, while the latest phase of the solvers might
    * be able to do something smarter with the more concise operation.
    */
  trait OperationN2 extends OperationN {
    override val numRequired: Int = 2

    def apply(i1: Term, i2: Term, is: Term*): Term = apply(i1 +: i2 +: is)

  }

  /**
   * Operations with variable number of arguments, at least three required
   */
  trait OperationN3 extends OperationN {
    override val numRequired: Int = 3

    def apply(i1: Term, i2: Term, i3: Term, is: Term*): Term = apply(i1 +: i2 +: i3 +: is)
  }
}
