package smtlib
package theories

import trees.Terms._
import Core._
import Ints._

/** Provide builders functions for all theories, which perform simplifications.
  *
  * We use the convention that capital letter operations (apply) do not perform
  * any syntactic simplification and build exactly the tree corresponding to
  * its definition, while corresponding functions with lower case letter can
  * potentially return a different representation than what it is called with.
  *
  * An example is the `And` vs `and` operation. The `And` needs a minimum of two
  * arguments, and will always produce a function application (and e1 e2 ...) with
  * the exact same element as provided. But the `and` constructor is more flexible
  * and will accept 0, 1 or more arguments, and will perform many simplifications. If
  * called with 0 argument, it would return `true`, while if called with 1 it would return
  * the element itself. Notice how in both case, even though you call the `and` constructor
  * you don't get an `and` in the resulting expression. Similarly, an `and` with many
  * arguments might simplify away `true` literals, or reduce the whole expression to
  * `false` if one element is `false`. The `And` apply method will always keep literals
  * without simplifying them away.
  *
  * So why not always use simplifying methods? First, they are slightly more expensive
  * than the corresponding capital letter constructors, as they will inspect the
  * expressions and do some processing on them. Second, there are times where you might
  * want precise control over the syntax, and having syntax-only methods as primitive
  * is very useful. One main difference is that those constructors perform some semantics
  * transformations, while capital letter constructors are purely syntactic.
  *
  * Finally note that one cannot assume anything more than semantics equivalence for the
  * returned term. The constructor is free to perform any sort of rewriting, so even
  * if you expect that calling and(true, false, x) should return false, it might still
  * return something like and(false, x). However, it will only return syntactically
  * correct term, so you would not get And(false). Usually, the above expression will
  * correctly get simplified to false, but the general way of thinking about these
  * constructors is as a best-effort simplification: it will do some relatively easy
  * and cheap simplification, but the exact contract does not specify the level of
  * simplification. This limitation is there as, in general, it is impossible to
  * properly specify the "correct" simplified form for a given formula.
  */
object Constructors {
    
  /*
   * We decide to not provide a varargs version that takes only 0 or 1 argument. The
   * reason is that we cannot forsee a use-case where a programmer would want to call
   * `and` with a statically known amount of argument 0 or 1, it would rather use the
   * corresponding simplified expression which is `true` or the single argument itself.
   *
   * However, cases with 0 or 1 argument could happen when and takes a Seq, as it is
   * possible that a program might just want to conjunct a dynamically sized list
   */
  def and(t1: Term, t2: Term, ts: Term*): Term = and(t1 +: t2 +: ts)
  def and(ts: Seq[Term]): Term = {
    val flat = ts.flatMap{
      case And(es@_*) => es
      case o => Seq(o)
    }

    var isFalse = false
    val simpler = ts.filter{
      case False() =>
        isFalse = true
        false
      case True() => false
      case _ => true
    }

    if(isFalse) False() else simpler match {
      case Seq() => True()
      case Seq(t) => t
      case _ => And(ts)
    }
  }

  def or(t1: Term, t2: Term, ts: Term*): Term = or(t1 +: t2 +: ts)
  def or(ts: Seq[Term]): Term = {
    val flat = ts.flatMap{
      case Or(es@_*) => es
      case o => Seq(o)
    }

    var isTrue = false
    val simpler = ts.filter{
      case True() =>
        isTrue = true
        false
      case False() => false
      case _ => true
    }

    if(isTrue) True() else simpler match {
      case Seq() => False()
      case Seq(t) => t
      case _ => Or(ts)
    }
  }

  def not(t: Term): Term = t match {
    case True() => False()
    case False() => True()

    case Not(s) => s
    case And(ts@_*) => or(ts map not)
    case Or(ts@_*) => and(ts map not)
    case Implies(t1, t2) => and(t1, not(t2))

    case LessThan(t1, t2) => GreaterEquals(t1, t2)
    case LessEquals(t1, t2) => GreaterThan(t1, t2)
    case GreaterThan(t1, t2) => LessEquals(t1, t2)
    case GreaterEquals(t1, t2) => LessThan(t1, t2)

    case _ => Not(t)
  }

}
