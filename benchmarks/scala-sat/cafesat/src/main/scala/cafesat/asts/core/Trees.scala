package cafesat.asts.core

object Trees {

  final case class PredicateSymbol(name: String, argSorts: List[Sort])
  final case class FunctionSymbol(name: String, argSorts: List[Sort], returnSort: Sort)
  final case class ConnectiveSymbol(name: String, arity: Int)
  final case class QuantifierSymbol(name: String)
  final case class TermQuantifierSymbol(name: String, argSorts: List[Sort], returnSort: Sort)

  final case class Sort(name: String, subSorts: List[Sort])

  sealed abstract class Term {
    val sort: Sort 

    override def toString = PrettyPrinter(this)
  }
  final case class FunctionApplication(fSymbol: FunctionSymbol, terms: List[Term]) extends Term {
    require(terms.size == fSymbol.argSorts.size)
    terms.zip(fSymbol.argSorts).foreach(c => c match {
      case (t,s) => require(t.sort == s)
    })

    val sort = fSymbol.returnSort

  }
  final case class Variable(name: String, sort: Sort) extends Term
  final case class ITE(condition: Formula, thenTerm: Term, elseTerm: Term) extends Term {
    require(thenTerm.sort == elseTerm.sort)
    val sort = thenTerm.sort
  }
  final case class TermQuantifierApplication(symbol: TermQuantifierSymbol, variable: Variable, terms: List[Term]) extends Term {
    require(terms.size == symbol.argSorts.size)
    terms.zip(symbol.argSorts).foreach(c => c match {
      case (t,s) => require(t.sort == s)
    })
    val sort = symbol.returnSort
  }

  sealed abstract class Formula {
    override def toString = PrettyPrinter(this)
  }

  final case class PredicateApplication(symbol: PredicateSymbol, terms: List[Term]) extends Formula 
  final case class ConnectiveApplication(symbol: ConnectiveSymbol, formulas: List[Formula]) extends Formula {
    require(symbol.arity >= 0 && symbol.arity == formulas.size)
  }
  final case class QuantifierApplication(symbol: QuantifierSymbol, variable: Variable, formula: Formula) extends Formula

  private var varCnt = -1
  private var funSymCnt = -1
  private var predSymCnt = -1

  //these function return fresh names with respect to all the previously returned fresh names. It could be the case,
  //if one is unlucky, that an existing name will clash with a name returned by these functions. They can be trusted
  //if all names are set via these.
  def freshFunctionSymbol(prefix: String, argSorts: List[Sort], returnSort: Sort): FunctionSymbol = {
    funSymCnt += 1
    FunctionSymbol(prefix + "_" + funSymCnt, argSorts, returnSort)
  }
  def freshFunctionSymbol(prefix: FunctionSymbol): FunctionSymbol = {
    val FunctionSymbol(name, argSorts, retSort) = prefix
    freshFunctionSymbol(name, argSorts, retSort)
  }
  def freshPredicateSymbol(prefix: String, argSorts: List[Sort]): PredicateSymbol = {
    predSymCnt += 1
    PredicateSymbol(prefix + "_" + predSymCnt, argSorts)
  }
  def freshPredicateSymbol(prefix: PredicateSymbol): PredicateSymbol = {
    val PredicateSymbol(name, argSorts) = prefix
    freshPredicateSymbol(name, argSorts)
  }

  def freshVariable(prefix: String, sort: Sort): Variable = { varCnt += 1; Variable(prefix + "_" + varCnt, sort) }
  def freshVariable(prefix: Variable): Variable = freshVariable(prefix.name, prefix.sort)

}
