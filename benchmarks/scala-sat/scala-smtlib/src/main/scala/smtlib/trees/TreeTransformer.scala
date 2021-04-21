package smtlib.trees

import Terms._
import Commands._
import CommandsResponses._

/** Transformer for any tree
  *
  * This is our most general transformer for trees, it
  * can be extended for specific needs by
  * overriding the context type C and the result type R, along with
  * the combine and transform methods.
  */
abstract class TreeTransformer {

  /*
   * The reason we need this general transformation framework
   * is because most of the trees have precise types, meaning
   * that a Term cannot appear where a Command is expected, and
   * that some parts have precise, non-compatible types, such
   * as attributes or keyword. It is thus not possible to define
   * a generic OperatorN deconstructor for Trees, if the goal is
   * to map the tree to a new, well-formed one. This object
   * defines the transform method for each of the type, and can
   * be overriden to match the exact mapping that is wanted by the
   * client.
   */

  /*
   * I need to figure out why we have an input context to the transformation
   * as it is currently not used (not depending on the return context). Maybe
   * it could be different type from the type returned, or maybe it
   * makes sense only when user override transform and modify the context
   * for the recursion (such as with a scope/symbol table)
   */

  /** Context computed while recursing down the trees */
  type C
  /** Result type computed at each tree */
  type R

  /** Combine the context with the results from subtrees
    *
    * combine is used after recursively transforming
    * the subtrees, to combine the multiple results into
    * one result to use in the post operation. The order
    * of the context is from left to right in the tree structure.
    *
    * Combine is always invoked, even on a single element sublist
    * or on an empty list. The tree argument is the current tree,
    * before applying the recursive transformation. Same for the
    * context argument, it is the current context at that transformation
    * step. So combine can be used to apply some function to each
    * tree element.
    */
  def combine(tree: Tree, context: C, results: Seq[R]): R

  def transform(term: Term, context: C): (Term, R) = {
    term match {
      case Let(vb, vbs, t) =>
        val (rvb, r1) = transform(vb, context)
        val (rvbs, r2s) = vbs.map(vb => transform(vb, context)).unzip
        val (rt, r3) = transform(t, context)
        (Let(rvb, rvbs, rt), combine(term, context, r1 +: r2s :+ r3))

      case Forall(sv, svs, t) =>
        val (rsv, c1) = transform(sv, context)
        val (rsvs, c2s) = svs.map(sv => transform(sv, context)).unzip
        val (rt, c3) = transform(t, context)
        (Forall(rsv, rsvs, rt), combine(term, context, c1 +: c2s :+ c3))
      case Exists(sv, svs, t) =>
        val (rsv, c1) = transform(sv, context)
        val (rsvs, c2s) = svs.map(sv => transform(sv, context)).unzip
        val (rt, c3) = transform(t, context)
        (Exists(rsv, rsvs, rt), combine(term, context, c1 +: c2s :+ c3))

      case AnnotatedTerm(t, attribute, attributes) =>
        val (rt, rc) = transform(t, context)
        (AnnotatedTerm(rt, attribute, attributes), combine(term, context, Seq(rc)))

      case FunctionApplication(fun, ts) =>
        val (funNew, funRes) = transformQualifiedIdentifier(fun, context)
        val (rts, cs) = ts.map(t => transform(t, context)).unzip
        (FunctionApplication(funNew, rts), combine(term, context, funRes +: cs))

      case (cst: Constant) => (cst, combine(cst, context, Seq()))

      case QualifiedIdentifier(id, sort) =>
        val (rid, c1) = transform(id, context)
        val rsort = sort.map(s => transform(s, context))
        (QualifiedIdentifier(rid, rsort.map(_._1)), 
         combine(term, context, c1 +: rsort.map(_._2).toSeq))

      case (ext: TermExtension) => ???
    }
  }

  def transform(sort: Sort, context: C): (Sort, R) = {
    val Sort(id, subSorts) = sort
    val (rid, c) = transform(id, context)
    val (rsubSorts, cs) = subSorts.map(s => transform(s, context)).unzip
    (Sort(rid, rsubSorts), combine(sort, context, c +: cs))
  }

  def transform(id: Identifier, context: C): (Identifier, R) = {
    val (newIdx, cs) = id.indices.map(index => transform(index, context)).unzip
    (Identifier(id.symbol, newIdx), combine(id, context, cs))
  }

  def transform(attr: Attribute, context: C): (Attribute, R) = {
    //TODO: maybe recurse into AttributeValue?
    (attr, combine(attr, context, Seq()))
  }

  def transform(option: SMTOption, context: C): (SMTOption, R) = {
    //TODO: should recurse into all options
    (option, combine(option, context, Seq()))
  }


  def transform(vb: VarBinding, context: C): (VarBinding, R) = {
    val (nt, nc) = transform(vb.term, context)
    (VarBinding(vb.name, nt), nc)
  }
  def transform(sv: SortedVar, context: C): (SortedVar, R) = {
    val (ns, nc) = transform(sv.sort, context)
    (SortedVar(sv.name, ns), nc)
  }

  def transform(sexpr: SExpr, context: C): (SExpr, R) = sexpr match {
    case SList(sexprs) =>
      val (nses, res) = sexprs.map(se => transform(se, context)).unzip
      (SList(nses), combine(sexpr, context, res))
    case (sym: SSymbol) => transformSymbol(sym, context)
    case _ => (sexpr, combine(sexpr, context, Seq()))
  }

  //some tree elements need their own transform name, because they
  //are a subtype of existing trees so overload won't work, and they
  //still need their own specific transformation for rebuilding
  //the tree properly
  def transformSymbol(symbol: SSymbol, context: C): (SSymbol, R) = (symbol, combine(symbol, context, Seq()))

  def transformQualifiedIdentifier(qid: QualifiedIdentifier, context: C): (QualifiedIdentifier, R) = {
    val (newId, res1) = transform(qid.id, context)
    val (newSort, res2) = qid.sort.map(s => transform(s, context)).map(p => (Some(p._1), Some(p._2))).getOrElse((None, None))

    (QualifiedIdentifier(newId, newSort), combine(qid, context, res1 +: res2.toSeq))
  }

  def transform(cmd: Command, context: C): (Command, R) = cmd match {
    case Assert(term) =>
      val (rt, rc) = transform(term, context)
      (Assert(rt), combine(cmd, context, Seq(rc)))

    case CheckSat() =>
      (CheckSat(), combine(cmd, context, Seq()))
    case CheckSatAssuming(propLiterals) =>
      val (rpls, resSyms) = propLiterals.map(pl => {
        val (ns, rs) = transformSymbol(pl.symbol, context)
        (PropLiteral(ns, pl.polarity), rs)
      }).unzip
      (CheckSatAssuming(rpls), combine(cmd, context, resSyms))

    case DeclareConst(name: SSymbol, sort: Sort) =>
      val (rn, rc1) = transformSymbol(name, context)
      val (rs, rc2) = transform(sort, context)
      (DeclareConst(rn, rs), combine(cmd, context, Seq(rc1, rc2)))

    case DeclareFun(name, paramSorts, returnSort) =>
      val (nameNew, nameRes) = transformSymbol(name, context)
      val (sortsNew, sortsRes) = paramSorts.map(s => transform(s, context)).unzip
      val (sortNew, sortRes) = transform(returnSort, context)
      val ndf = DeclareFun(nameNew, sortsNew, sortNew)
      (ndf, combine(cmd, context, nameRes +: sortsRes :+ sortRes))

    case DeclareSort(name, arity) =>
      val (nameNew, nameRes) = transformSymbol(name, context)
      (DeclareSort(nameNew, arity), combine(cmd, context, Seq(nameRes)))

    case DefineFun(fd) =>
      val (nfd, subRes) = transformFunDef(fd, context)
      val ndf = DefineFun(nfd)
      (ndf, combine(cmd, context, subRes))

    case DefineFunRec(fd) =>
      val (nfd, subRes) = transformFunDef(fd, context)
      val ndfr = DefineFunRec(nfd)
      (ndfr, combine(cmd, context, subRes))

    case DefineFunsRec(funDecls: Seq[FunDec], bodies: Seq[Term]) =>
      val (nfds, subRes1) = funDecls.map(fd => transformFunDec(fd, context)).unzip
      val (nbs, subRes2) = bodies.map(b => transform(b, context)).unzip
      val ndfrs = DefineFunsRec(nfds, nbs)
      (ndfrs, combine(cmd, context, subRes1.flatten ++ subRes2))

    case DefineSort(name, params, sort) =>
      val (nameNew, nameRes) = transformSymbol(name, context)
      val (paramsNew, paramsRes) = params.map(s => transformSymbol(s, context)).unzip
      val (sortNew, sortRes) = transform(sort, context)
      val nds = DefineSort(nameNew, paramsNew, sortNew)
      (nds, combine(cmd, context, nameRes +: paramsRes :+ sortRes))

    case Echo(value: SString) =>
      (Echo(value), combine(cmd, context, Seq()))

    case Exit() => (cmd, combine(cmd, context, Seq()))

    case GetAssertions() => (cmd, combine(cmd, context, Seq()))
    case GetAssignment() => (cmd, combine(cmd, context, Seq()))

    case GetInfo(_) => (cmd, combine(cmd, context, Seq()))
    case GetModel() => (cmd, combine(cmd, context, Seq()))
    case GetOption(_) => (cmd, combine(cmd, context, Seq()))
    case GetProof() => (cmd, combine(cmd, context, Seq()))
    case GetUnsatAssumptions() => (cmd, combine(cmd, context, Seq()))
    case GetUnsatCore() => (cmd, combine(cmd, context, Seq()))

    case GetValue(term: Term, terms: Seq[Term]) =>
      val (nt, res1) = transform(term, context)
      val (nts, res2) = terms.map(t => transform(t, context)).unzip
      (GetValue(nt, nts), combine(cmd, context, res1 +: res2))

    case Pop(_) => (cmd, combine(cmd, context, Seq()))
    case Push(_) => (cmd, combine(cmd, context, Seq()))

    case Reset() => (cmd, combine(cmd, context, Seq()))
    case ResetAssertions() => (cmd, combine(cmd, context, Seq()))

    case SetInfo(_) => (cmd, combine(cmd, context, Seq()))
    case SetLogic(_) => (cmd, combine(cmd, context, Seq()))
    case SetOption(_) => (cmd, combine(cmd, context, Seq()))

    case (ext: CommandExtension) => ext.transform(this)(context)

  ////non standard declare-datatypes (no support for parametric types)
  //case class DeclareDatatypes(datatypes: Seq[(SSymbol, Seq[Constructor])]) extends Command
  }

  def transform(resp: CommandResponse, context: C): (CommandResponse, R) = resp match {
    case _ => ???
  }

  //this transforms the fundef with recursive calls, but does not combine the result
  //as we do not consider FunDef to be a tree
  private def transformFunDef(fd: FunDef, context: C): (FunDef, Seq[R]) = {
    val FunDef(name, params, sort, body) = fd
    val (nameNew, nameRes) = transformSymbol(name, context)
    val (paramsNew, paramsRes) = params.map(s => transform(s, context)).unzip
    val (sortNew, sortRes) = transform(sort, context)
    val (bodyNew, bodyRes) = transform(body, context)
    (FunDef(nameNew, paramsNew, sortNew, bodyNew), nameRes +: paramsRes :+ sortRes :+ bodyRes)
  }

  //for same reasons, FunDec is not a tree, just a syntactic wrapper
  private def transformFunDec(fd: FunDec, context: C): (FunDec, Seq[R]) = {
    val FunDec(name, params, sort) = fd
    val (nameNew, nameRes) = transformSymbol(name, context)
    val (paramsNew, paramsRes) = params.map(sortedVar => transform(sortedVar, context)).unzip
    val (sortNew, sortRes) = transform(sort, context)
    (FunDec(nameNew, paramsNew, sortNew), nameRes +: paramsRes :+ sortRes)
  }

}

/** A tree transformer with pre/post transformation
  *
  * This extends the generic TreeTransformer by adding pre and
  * post transformation to be applied before and after the
  * recursive transformations. The core transform becomes final,
  * as it cannot be extended easily due to the wrapping of pre/post
  * around it. Most basic transformation will work by implementing
  * either of pre or post.
  */
abstract class PrePostTreeTransformer extends TreeTransformer {

  /** a pre-transformation to be applied to the term
    *
    * The term will be mapped
    * before performing the recursion in the subtrees. This
    * should only do the mapping, without any recursive
    * call.
    */
  def pre(term: Term, context: C): (Term, C)

  /** a post-transformation to be applied to the term
    *
    * The term will be mapped
    * after performing the recursion in the subtrees. This
    * should only do the mapping, without any recursive
    * call.
    */
  def post(term: Term, result: R): (Term, R)

  final override def transform(term: Term, context: C): (Term, R) = {
    val (preTerm, preContext) = pre(term, context)
    val (postTerm, postContext) = super.transform(preTerm, preContext)
    post(postTerm, postContext)
  }

  def pre(sort: Sort, context: C): (Sort, C)
  def post(sort: Sort, result: R): (Sort, R)
  final override def transform(sort: Sort, context: C): (Sort, R) = {
    val (preSort, preContext) = pre(sort, context)
    val (postSort, postResult) = super.transform(preSort, preContext)
    post(postSort, postResult)
  }

}

/** a tree transformer without carrying a context */
abstract class SimpleTreeTransformer extends PrePostTreeTransformer {
  type C = Unit
  type R = Unit

  def pre(term: Term): Term
  def post(term: Term): Term
  def pre(sort: Sort): Sort
  def post(sort: Sort): Sort

  final override def combine(tree: Tree, c: C, cs: Seq[R]): R = ()

  final override def pre(term: Term, c: C): (Term, C) = (pre(term), ())
  final override def post(term: Term, r: R): (Term, R) = (post(term), ())
  final override def pre(sort: Sort, c: C): (Sort, C) = (pre(sort), ())
  final override def post(sort: Sort, c: R): (Sort, R) = (post(sort), ())

  final def transform(term: Term): Term = transform(term, ())._1
  final def transform(sort: Sort): Sort = transform(sort, ())._1

  override final def transform(id: Identifier, c: C): (Identifier, R) = super.transform(id, c)
  final def transform(id: Identifier): Identifier = transform(id, ())._1

  override final def transform(varBinding: VarBinding, c: C): (VarBinding, R) = super.transform(varBinding, c)
  final def transform(varBinding: VarBinding): VarBinding = transform(varBinding, ())._1

  override final def transform(sortedVar: SortedVar, c: C): (SortedVar, R) = super.transform(sortedVar, c)
  final def transform(sortedVar: SortedVar): SortedVar = transform(sortedVar, ())._1

}

abstract class TreeFolder extends TreeTransformer {

  type C = Unit

  def combine(tree: Tree, accs: Seq[R]): R
  override final def combine(tree: Tree, context: Unit, results: Seq[R]): R = {
    combine(tree, results)
  }

  final def fold(tree: Tree): R = tree match {
    case (term: Term) => transform(term, ())._2
    case (s: Sort) => transform(s, ())._2
    case (id: Identifier) => transform(id, ())._2
    case (vb: VarBinding) => transform(vb, ())._2
    case (sv: SortedVar) => transform(sv, ())._2
    case (cmd: Command) => transform(cmd, ())._2
    case (resp: CommandResponse) => transform(resp, ())._2
    case (attr: Attribute) => transform(attr, ())._2
    case (opt: SMTOption) => transform(opt, ())._2
    case (e: SExpr) => transform(e, ())._2
  }
}

abstract class TreeTraverser extends PrePostTreeTransformer {

  type C = Unit
  type R = Unit

  def pre(term: Term): Unit = ()
  def post(term: Term): Unit = ()

  def pre(sort: Sort): Unit = ()
  def post(sort: Sort): Unit = ()

  def combine(tree: Tree): Unit

  override final def combine(tree: Tree, c: Unit, cs: Seq[Unit]): Unit = combine(tree)

  override final def pre(term: Term, c: C): (Term, C) = {
    pre(term)
    (term, ())
  }
  override final def post(term: Term, r: R): (Term, R) = {
    post(term)
    (term, ())
  }
  override final def pre(sort: Sort, c: C): (Sort, C) = {
    pre(sort)
    (sort, ())
  }
  override final def post(sort: Sort, r: R): (Sort, R) = {
    post(sort)
    (sort, ())
  }

  final def traverse(tree: Tree): Unit = tree match {
    case (t: Term) => transform(t, ())
    case (s: Sort) => transform(s, ())
    case (id: Identifier) => transform(id, ())
    case (vb: VarBinding) => transform(vb, ())
    case (sv: SortedVar) => transform(sv, ())
    case (cmd: Command) => transform(cmd, ())
    case (resp: CommandResponse) => transform(resp, ())
    case (attr: Attribute) => transform(attr, ())
    case (opt: SMTOption) => transform(opt, ())
    case (e: SExpr) => transform(e, ())
  }

}
