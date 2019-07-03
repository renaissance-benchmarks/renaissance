package cafesat.asts.core

import Trees._

import scala.collection.mutable.ListBuffer
// when we apply some function to a quantified term, it does not affect the bound variables
// If a map modify the quantified variable, we should maybe propagate in the bound term?
// TODO: alpha renaming

object Manip {

  def mapPreorder(t: Term, ff: (Formula) => Formula, ft: (Term) => Term): Term = mapPreorder(t, ff, ft, Nil)
  private def mapPreorder(t: Term, ff: (Formula) => Formula, ft: (Term) => Term, bv: List[Variable]): Term = t match {
    case v@Variable(_,_) if (bv.contains(v)) => v
    case _ => ft(t) match {
      case v@Variable(_, _) => v
      case FunctionApplication(s, ts) => {
        val res = FunctionApplication(s, ts.map(t => mapPreorder(t, ff, ft, bv)))
        res
      }
      case ITE(c, t, e) => {
        val newC = mapPreorder(c, ff, ft, bv)
        val newT = mapPreorder(t, ff, ft, bv)
        val newE = mapPreorder(e, ff, ft, bv)
        ITE(newC, newT, newE)
      }
      case TermQuantifierApplication(s, v, ts) => TermQuantifierApplication(s, v, ts.map(t => mapPreorder(t, ff, ft, v :: bv)))
    }
  }

  def mapPostorder(t: Term, ff: (Formula) => Formula, ft: (Term) => Term): Term = mapPostorder(t, ff, ft, Nil)
  private def mapPostorder(t: Term, ff: (Formula) => Formula, ft: (Term) => Term, bv: List[Variable]): Term = t match {
    case v@Variable(_, _) if bv.contains(v) => v
    case v@Variable(_, _) => ft(v)
    case FunctionApplication(s, ts) => {
      var newArgs: ListBuffer[Term] = new ListBuffer
      var oldArgs: List[Term] = ts
      while(!oldArgs.isEmpty) {
        newArgs.append(mapPostorder(oldArgs.head, ff, ft, bv))
        oldArgs = oldArgs.tail
      }
      ft(FunctionApplication(s, newArgs.toList))
    }
    case ITE(c, t, e) => {
      val newC = mapPostorder(c, ff, ft, bv)
      val newT = mapPostorder(t, ff, ft, bv)
      val newE = mapPostorder(e, ff, ft, bv)
      ft(ITE(newC, newT, newE))
    }
    case TermQuantifierApplication(s, v, ts) => ft(TermQuantifierApplication(s, v, ts.map(t => mapPostorder(t, ff, ft, v :: bv))))
  }

  def mapPreorder(f: Formula, ff: (Formula) => Formula, ft: (Term) => Term): Formula = mapPreorder(f, ff, ft, Nil)
  private def mapPreorder(f: Formula, ff: (Formula) => Formula, ft: (Term) => Term, bv: List[Variable]): Formula = ff(f) match {
    case PredicateApplication(s, ts) => PredicateApplication(s, ts.map(t => mapPreorder(t, ff, ft, bv)))
    case ConnectiveApplication(s, fs) => ConnectiveApplication(s, fs.map(f => mapPreorder(f, ff, ft, bv)))
    case QuantifierApplication(s, v, f) => QuantifierApplication(s, v, mapPreorder(f, ff, ft, v :: bv))
  }

  def mapPostorder(f: Formula, ff: (Formula) => Formula, ft: (Term) => Term): Formula = mapPostorder(f, ff, ft, Nil)
  private def mapPostorder(f: Formula, ff: (Formula) => Formula, ft: (Term) => Term, bv: List[Variable]): Formula = f match {
    case PredicateApplication(s, ts) => {
      var newArgs: ListBuffer[Term] = new ListBuffer
      var oldArgs: List[Term] = ts
      while(!oldArgs.isEmpty) {
        newArgs.append(mapPostorder(oldArgs.head, ff, ft, bv))
        oldArgs = oldArgs.tail
      }
      ff(PredicateApplication(s, newArgs.toList))
    }
    case ConnectiveApplication(s, fs) => {
      var newArgs: ListBuffer[Formula] = new ListBuffer
      var oldArgs = fs
      while(!oldArgs.isEmpty) {
        newArgs.append(mapPostorder(oldArgs.head, ff, ft, bv))
        oldArgs = oldArgs.tail
      }
      ff(ConnectiveApplication(s, newArgs.toList))
    }
    case QuantifierApplication(s, v, f) => ff(QuantifierApplication(s, v, mapPostorder(f, ff, ft, v :: bv)))
  }


  def foldPreorder[A](t: Term, z: A)(ff: (A, Formula) => A, ft: (A, Term) => A): A = foldPreorder(t, z, Nil)(ff, ft)
  def foldPreorder[A](t: Term, z: A, bv: List[Variable])(ff: (A, Formula) => A, ft: (A, Term) => A): A = t match {
    case v@Variable(_, _) if bv.contains(v) => z
    case v@Variable(_, _) => ft(z, v)
    case fa@FunctionApplication(_, ts) => {
      val tmp = ft(z, fa)
      ts.foldLeft(tmp)((a, t) => foldPreorder(t, a, bv)(ff, ft))
    }
    case ite@ITE(c, t, e) => {
      val tmp1 = ft(z, ite)
      val tmp2 = foldPreorder(c, tmp1, bv)(ff, ft)
      val tmp3 = foldPreorder(t, tmp2, bv)(ff, ft)
      foldPreorder(e, tmp3, bv)(ff, ft)
    }
    case tq@TermQuantifierApplication(s, v, ts) => {
      val tmp = ft(z, tq)
      ts.foldLeft(tmp)((a, t) => foldPreorder(t, a, v :: bv)(ff, ft))
    }
  }

  def foldPostorder[A](t: Term, z: A)(ff: (A, Formula) => A, ft: (A, Term) => A): A = foldPostorder(t, z, Nil)(ff, ft)
  def foldPostorder[A](t: Term, z: A, bv: List[Variable])(ff: (A, Formula) => A, ft: (A, Term) => A): A = t match {
    case v@Variable(_, _) if bv.contains(v) => z
    case v@Variable(_, _) => ft(z, v)
    case fa@FunctionApplication(_, ts) => {
      val tmp = ts.foldLeft(z)((a, t) => foldPostorder(t, a, bv)(ff, ft))
      ft(tmp, fa)
    }
    case ite@ITE(c, t, e) => {
      val tmp1 = foldPostorder(c, z, bv)(ff, ft)
      val tmp2 = foldPostorder(t, tmp1, bv)(ff, ft)
      val tmp3 = foldPostorder(e, tmp2, bv)(ff, ft)
      ft(tmp3, ite)
    }
    case tq@TermQuantifierApplication(s, v, ts) => {
      val tmp = ts.foldLeft(z)((a, t) => foldPostorder(t, a, v :: bv)(ff, ft))
      ft(tmp, tq)
    }
  }

  def foldPreorder[A](f: Formula, z: A)(ff: (A, Formula) => A, ft: (A, Term) => A): A = foldPreorder(f, z, Nil)(ff, ft)
  def foldPreorder[A](f: Formula, z: A, bv: List[Variable])(ff: (A, Formula) => A, ft: (A, Term) => A): A = f match {
    case p@PredicateApplication(_, ts) => {
      val tmp = ff(z, p)
      ts.foldLeft(tmp)((a, t) => foldPreorder(t, a, bv)(ff, ft))
    }
    case c@ConnectiveApplication(_, fs) => {
      val tmp = ff(z, c)
      fs.foldLeft(tmp)((a, f) => foldPreorder(f, a, bv)(ff, ft))
    }
    case q@QuantifierApplication(_, v, f) => {
      val tmp = ff(z, q)
      foldPreorder(f, tmp, v :: bv)(ff, ft)
    }
  }

  def foldPostorder[A](f: Formula, z: A)(ff: (A, Formula) => A, ft: (A, Term) => A): A = foldPostorder(f, z, Nil)(ff, ft)
  def foldPostorder[A](f: Formula, z: A, bv: List[Variable])(ff: (A, Formula) => A, ft: (A, Term) => A): A = f match {
    case p@PredicateApplication(_, ts) => {
      val tmp = ts.foldLeft(z)((a, t) => foldPreorder(t, a, bv)(ff, ft))
      ff(tmp, p)
    }
    case c@ConnectiveApplication(_, fs) => {
      val tmp = fs.foldLeft(z)((a, f) => foldPreorder(f, a, bv)(ff, ft))
      ff(tmp, c)
    }
    case q@QuantifierApplication(_, v, f) => {
      val tmp = foldPreorder(f, z, v :: bv)(ff, ft)
      ff(tmp, q)
    }
  }

  def foreachPreorder(t: Term, ff: (Formula) => Unit, ft: (Term) => Unit): Unit = foldPreorder(t, ())((_,f) => ff(f), (_,t) => ft(t))
  def foreachPreorder(f: Formula, ff: (Formula) => Unit, ft: (Term) => Unit): Unit = foldPreorder(f, ())((_, f) => ff(f), (_, t) => ft(t))

  def foreachPostorder(t: Term, ff: (Formula) => Unit, ft: (Term) => Unit): Unit = foldPostorder(t, ())((_, f) => ff(f), (_, t) => ft(t))
  def foreachPostorder(f: Formula, ff: (Formula) => Unit, ft: (Term) => Unit): Unit = foldPostorder(f, ())((_, f) => ff(f), (_, t) => ft(t))

  def exists(t: Term, pf: (Formula) => Boolean, pt: (Term) => Boolean): Boolean = foldPostorder(t, false)((b, f) => b || pf(f), (b, t) => (b || pt(t)))
  def exists(f: Formula, pf: (Formula) => Boolean, pt: (Term) => Boolean): Boolean = foldPostorder(f, false)((b, f) => b || pf(f), (b, t) => (b || pt(t)))
  def exists(t: Term, pt: (Term) => Boolean): Boolean = exists(t, (_: Formula) => false, pt)
  def exists(f: Formula, pf: (Formula) => Boolean): Boolean = exists(f, pf, (_: Term) => false)

  def forall(t: Term, pf: (Formula) => Boolean, pt: (Term) => Boolean): Boolean = foldPostorder(t, true)((b, f) => b && pf(f), (b, t) => (b && pt(t)))
  def forall(f: Formula, pf: (Formula) => Boolean, pt: (Term) => Boolean): Boolean = foldPostorder(f, true)((b, f) => b && pf(f), (b, t) => (b && pt(t)))
  def forall(t: Term, pt: (Term) => Boolean): Boolean = forall(t, (_: Formula) => true, pt)
  def forall(f: Formula, pf: (Formula) => Boolean): Boolean = forall(f, pf, (_: Term) => true)

  def count(t: Term, pf: (Formula) => Boolean, pt: (Term) => Boolean): Int = foldPostorder(t, 0)(
    (a, f) => if(pf(f)) a + 1 else a, 
    (a, t) => if(pt(t)) a + 1 else a)
  def count(f: Formula, pf: (Formula) => Boolean, pt: (Term) => Boolean): Int = foldPostorder(f, 0)(
    (a, f) => if(pf(f)) a + 1 else a,
    (a, t) => if(pt(t)) a + 1 else a)
  def count(t: Term, pt: (Term) => Boolean): Int = count(t, (_: Formula) => false, pt)
  def count(f: Formula, pf: (Formula) => Boolean): Int = count(f, pf, (_: Term) => false)

  def size(t: Term): Int = count(t, (f: Formula) => true, (t: Term) => true)
  def size(f: Formula): Int = count(f, (f: Formula) => true, (t: Term) => true)

  def vars(t: Term): Set[Variable] = foldPostorder(t, Set[Variable]())((a, f) => a, (a, t) => t match {
      case v@Variable(_, _) => a + v
      case _ => a
    })
  def vars(f: Formula): Set[Variable] = foldPostorder(f, Set[Variable]())((a, f) => a, (a, t) => t match {
      case v@Variable(_, _) => a + v
      case _ => a
    })


  def substitute(t: Term, m: Map[Variable, Term]): Term = mapPostorder(t, f => f, t => t match {
    case v@Variable(_,_) => m.get(v) match {
      case Some(a) => a
      case None => v
    }
    case t@_ => t
  })
  def substitute(t: Term, oldVar: Variable, newT: Term): Term = substitute(t, Map(oldVar -> newT))
  def substitute(f: Formula, m: Map[Variable, Term]): Formula = mapPostorder(f, f => f, t => t match {
    case v@Variable(_, _) => m.get(v) match {
      case Some(a) => a
      case None => v
    }
    case t@_ => t
  })
  def substitute(f: Formula, oldVar: Variable, newT: Term): Formula = substitute(f, Map(oldVar -> newT))

  def contains(t: Term, elem: Term): Boolean = foldPostorder(t, false)((b, f) => false,(b, t2) => b || elem == t2)
  def contains(f: Formula, elem: Term): Boolean = foldPostorder(f, false)((b, f) => false, (b, t2) => b || elem == t2)


  //find a node that verify a predicate and apply a function on it and return. Only find one such element even if several are present
  private def findAndMap(f: Formula, pf: (Formula) => Boolean, pt: (Term) => Boolean, ff: (Formula) => Formula, ft: (Term) => Term, bv: List[Variable]): (Formula, Boolean) = if(pf(f)) (ff(f), true) else (f match {
    case PredicateApplication(s, ts) => {
      var found = false
      val rts = ts.map(t => {
        if(found)
          t
        else {
          val (nt, b) = findAndMap(t, pf, pt, ff, ft, bv)
          found = b
          nt
        }
      })
      (PredicateApplication(s, rts), found)
    }
    case ConnectiveApplication(s, fs) => {
      var found = false
      val rts = fs.map(f => {
        if(found)
          f
        else {
          val (nf, b) = findAndMap(f, pf, pt, ff, ft, bv)
          found = b
          nf
        }
      })
      (ConnectiveApplication(s, rts), found)
    }
    case QuantifierApplication(s, v, f) => {
      val (nf, found) = findAndMap(f, pf, pt, ff, ft, v :: bv)
      (QuantifierApplication(s, v, nf), found)
    }
  })
  private def findAndMap(t: Term, pf: (Formula) => Boolean, pt: (Term) => Boolean, ff: (Formula) => Formula, ft: (Term) => Term, bv: List[Variable]): (Term, Boolean) = t match {
    case v@Variable(_,_) if (bv.contains(v)) => (v, false)
    case _ => if(pt(t)) (ft(t), true) else (t match {
      case v@Variable(_, _) => (v, false)
      case FunctionApplication(s, ts) => {
        var found = false
        val rts = ts.map(t => {
          if(found)
            t
          else {
            val (nt, b) = findAndMap(t, pf, pt, ff, ft, bv)
            found = b
            nt
          }
        })
        (FunctionApplication(s, rts), found)
      }
      case ITE(c, t, e) => {
        val (newC, b1) = findAndMap(c, pf, pt, ff, ft, bv)
        if(b1) 
          (ITE(newC, t, e), true)
        else {
          val (newT, b2) = findAndMap(t, pf, pt, ff, ft, bv)
          if(b2)
            (ITE(newC, newT, e), true)
          else {
            val (newE, b3) = findAndMap(e, pf, pt, ff, ft, bv)
            (ITE(newC, newT, newE), b3)
          }
        }
      }
      case TermQuantifierApplication(s, v, ts) => sys.error("not supported")
    })
  }
  def findAndMap(f: Formula, pf: (Formula) => Boolean, pt: (Term) => Boolean, ff: (Formula) => Formula, ft: (Term) => Term): (Formula, Boolean) = 
    findAndMap(f, pf, pt, ff, ft, List())
  def findAndMap(t: Term, pf: (Formula) => Boolean, pt: (Term) => Boolean, ff: (Formula) => Formula, ft: (Term) => Term): (Term, Boolean) = 
    findAndMap(t, pf, pt, ff, ft, List())


  def alphaRenaming(formula: Formula): Formula = {
    var globalVars: Map[Variable, Variable] = Map()
    def recForm(f: Formula, bv: Map[Variable, Variable]): Formula = f match {
      case QuantifierApplication(s, v, b) => {
        val newName = freshVariable(v)
        QuantifierApplication(s, newName, recForm(b, bv + (v -> newName)))
      }
      case PredicateApplication(s, ts) => PredicateApplication(s, ts.map(t => recTerm(t, bv)))
      case ConnectiveApplication(s, fs) => ConnectiveApplication(s, fs.map(f => recForm(f, bv)))
    }
    def recTerm(t: Term, bv: Map[Variable, Variable]): Term = t match {
      case v@Variable(_,_) => bv.get(v) match {
        case Some(nv) => nv
        case None => globalVars.get(v) match {
          case Some(nv) => nv
          case None => {
            val nv = freshVariable(v)
            globalVars += (v -> nv)
            nv
          }
        }
      }
      case FunctionApplication(s, ts) => FunctionApplication(s, ts.map(t => recTerm(t, bv)))
      case ITE(c, t, e) => ITE(recForm(c, bv), recTerm(t, bv), recTerm(e, bv))
      case TermQuantifierApplication(s, v, ts) => sys.error("TODO")
    }

    recForm(formula, Map())
  }

}
