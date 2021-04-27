package smtlib
package extensions.tip

import printer._
import trees.Terms._
import trees.Commands._
import trees.TreeTransformer

object Terms {
  case class Lambda(args: Seq[SortedVar], body: Term) extends TermExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(lambda ")
      ctx.printNary(args, "(", " ", ") ")
      ctx.print(body)
      ctx.print(")")
    }
  }

  case class Application(caller: Term, args: Seq[Term]) extends TermExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(@ ")
      ctx.printNary(caller +: args, "", " ", ")")
    }
  }

  case class Match(scrut: Term, cases: Seq[Case]) extends TermExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(match ")
      ctx.print(scrut)
      ctx.printNary(cases, (cse: Case) => {
        ctx.print("(case ")
        cse.pattern match {
          case Default => ctx.print("default")
          case CaseObject(sym) => ctx.print(sym)
          case CaseClass(sym, args) => ctx.printNary(sym +: args, "(", " ", ")")
        }
        ctx.print(" ")
        ctx.print(cse.rhs)
        ctx.print(")")
      }, " ", " ", ")")
    }
  }

  case class Case(pattern: Pattern, rhs: Term)

  sealed trait Pattern
  case object Default extends Pattern 
  case class CaseObject(sym: SSymbol) extends Pattern
  case class CaseClass(sym: SSymbol, binders: Seq[SSymbol]) extends Pattern

  case class FunDecPar(tps: Seq[SSymbol], name: SSymbol, params: Seq[SortedVar], returnSort: Sort)
}

object Commands {
  import Terms._

  case class AssertPar(tps: Seq[SSymbol], term: Term) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(assert (par ")
      ctx.printNary(tps, "(", " ", ") ")
      ctx.print(term)
      ctx.print("))\n")
    }
    def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ???
  }

  case class DeclareConstPar(tps: Seq[SSymbol], sym: SSymbol, sort: Sort) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(declare-const (par ")
      ctx.printNary(tps, "(", " ", ") ")
      ctx.print("(")
      ctx.print(sym)
      ctx.print(" ")
      ctx.print(sort)
      ctx.print(")))\n")
    }
    def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ???
  }

  case class DeclareFunPar(tps: Seq[SSymbol], sym: SSymbol, argSorts: Seq[Sort], returnSort: Sort) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(declare-fun (par ")
      ctx.printNary(tps, "(", " ", ") ")
      ctx.print("(")
      ctx.print(sym)
      ctx.printNary(argSorts, " (", " ", ") ")
      ctx.print(returnSort)
      ctx.print(")))\n")
    }
    def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ???
  }

  case class DefineFunPar(tps: Seq[SSymbol], fd: FunDef) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(define-fun (par ")
      ctx.printNary(tps, "(", " ", ") ")
      ctx.print("(")
      ctx.print(fd.name)
      ctx.printNary(fd.params, " (", " ", ") ")
      ctx.print(fd.returnSort)
      ctx.print(" ")
      ctx.print(fd.body)
      ctx.print(")))\n")
    }
    def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ???
  }

  case class DefineFunRecPar(tps: Seq[SSymbol], fd: FunDef) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(define-fun-rec (par ")
      ctx.printNary(tps, "(", " ", ") ")
      ctx.print("(")
      ctx.print(fd.name)
      ctx.printNary(fd.params, " (", " ", ") ")
      ctx.print(fd.returnSort)
      ctx.print(" ")
      ctx.print(fd.body)
      ctx.print(")))\n")
    }
    def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ???
  }

  case class DefineFunsRecPar(fds: Seq[Either[FunDecPar, FunDec]], bodies: Seq[Term]) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(define-funs-rec ")
      ctx.printNary(fds, (fd: Either[FunDecPar, FunDec]) => fd match {
        case Left(FunDecPar(tps, name, params, returnSort)) =>
          ctx.print("(par ")
          ctx.printNary(tps, "(", " ", ") ")
          ctx.print("(")
          ctx.print(name)
          ctx.printNary(params, " (", " ", ") ")
          ctx.print(returnSort)
          ctx.print("))")
        case Right(FunDec(name, params, returnSort)) =>
          ctx.print("(")
          ctx.print(name)
          ctx.printNary(params, " (", " ", ") ")
          ctx.print(returnSort)
          ctx.print(")")
      }, "(", " ", ") ")
      ctx.printNary(bodies, "(", " ", "))\n")
    }
    def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ???
  }

  case class DeclareDatatypesPar(tps: Seq[SSymbol], datatypes: Seq[(SSymbol, Seq[Constructor])]) extends CommandExtension {
    def print(ctx: PrintingContext): Unit = {
      ctx.print("(declare-datatypes ")
      ctx.printNary(tps, "(", " ", ") ")
      ctx.printNary(datatypes, (datatype: (SSymbol, Seq[Constructor])) => {
        ctx.print("(")
        ctx.print(datatype._1.name)
        if (datatype._2.nonEmpty) ctx.printNary(datatype._2, (constructor: Constructor) => {
          ctx.print("(")
          ctx.print(constructor.sym.name)
          if (constructor.fields.nonEmpty) ctx.printNary(constructor.fields, (field: (SSymbol, Sort)) => {
            ctx.print("(")
            ctx.print(field._1.name)
            ctx.print(" ")
            ctx.print(field._2)
            ctx.print(")")
          }, " ", " ", "")
          ctx.print(")")
        }, " ", " ", "")
        ctx.print(")")
      }, "(", " ", "))\n")
    }
    def transform(tt: TreeTransformer)(context: tt.C): (Command, tt.R) = ???
  }
}

