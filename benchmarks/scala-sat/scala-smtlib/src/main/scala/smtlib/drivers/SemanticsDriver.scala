package smtlib
package drivers

import trees.Terms._
import trees.Commands._
import trees.CommandsResponses._
import printer.RecursivePrinter


/** Provide standard complient behaviour for a sequence of commands.
  *
  * This driver will properly understand the whole SMT-LIB 2.5 language,
  * maintaining proper state and forwarding work to an underlying solver.
  * The behaviour of this driver is to perfectly follow the standard, and
  * properly abstract the peculiarities of the black box solvers so that
  * they can be used with SMT-LIB 2.5 language.
  *
  * One difficult in implementing the SMT-LIB standard is that the standard
  * is designed for process interaction, relying on both a standard output and
  * standard error channel. Standard output and error are part of the interface
  * of the driver, and by default will be available on the driver. If one sets
  * the :diagnostic-output-channel or :regular-output-channel options, that
  * will redirect this behaviour and send the outputs to files.
  * Basically: stdout and stderr are the iterator attached to this driver.
  *
  * TODO: this is work in progress, not usable yet.
  */
class SemanticsDriver(
  rawSolver: Interpreter,
  onRegularOutput: (CommandResponse) => Unit,
  onDiagnosticOutput: (String) => Unit
) {

  import SemanticsDriver._

  private var regularOutputChannel: (CommandResponse) => Unit = onRegularOutput
  private var diagnosticOutputChannel: (String) => Unit = onDiagnosticOutput

  private def fileRegularOutputChannel(name: String): (CommandResponse) => Unit = {
    val f = new java.io.FileWriter(name)
    (res: CommandResponse) => {
      f.write(RecursivePrinter.toString(res))
      f.write("\n")
    }
  }
  private def fileDiagnosticOutputChannel(name: String): (String) => Unit = {
    val f = new java.io.FileWriter(name)
    (info: String) => {
      f.write(info)
      f.write("\n")
    }
  }

  private var executionMode: ExecutionMode = StartMode
  
  private var logic: Option[Logic] = None
  private var printSuccess = true
  private var globalDeclarations = false
  private var produceModels = false

  private def doPrintSuccess(): Unit = {
    if(printSuccess)
      onRegularOutput(Success)
  }

  protected def processSetOption(option: SMTOption): Unit = option match {

    case DiagnosticOutputChannel(value) =>
      //TODO: can we set stdout for diagnostic output channel and redirect it to regular ?
      if(value == "stderr")
        diagnosticOutputChannel = onDiagnosticOutput
      else
        diagnosticOutputChannel = fileDiagnosticOutputChannel(value)
      doPrintSuccess()


    case GlobalDeclarations(value) =>
      if(executionMode != StartMode) {
        regularOutputChannel(Error("global-declaration can only be set in Start mode"))
      } else {
        globalDeclarations = value
        rawSolver.eval(SetOption(option))
        doPrintSuccess()
      }

    case InteractiveMode(value) => 
      regularOutputChannel(Unsupported)

    case PrintSuccess(value) =>
      printSuccess = value
      doPrintSuccess()

    case ProduceAssertions(value) =>
      regularOutputChannel(Unsupported)

    case ProduceAssignments(value) =>
      regularOutputChannel(Unsupported)

    case ProduceModels(value) =>
      if(executionMode != StartMode) {
        regularOutputChannel(Error("produce-models can only be set in Start mode"))
      } else {
        produceModels = value
        rawSolver.eval(SetOption(option))
        doPrintSuccess()
      }

    case ProduceProofs(value) =>
      regularOutputChannel(Unsupported)

    case ProduceUnsatAssumptions(value) =>
      regularOutputChannel(Unsupported)

    case ProduceUnsatCores(value) =>
      regularOutputChannel(Unsupported)

    case RandomSeed(value) =>
      regularOutputChannel(Unsupported)

    case RegularOutputChannel(value) =>
      if(value == "stdout")
        regularOutputChannel = onRegularOutput
      else
        regularOutputChannel = fileRegularOutputChannel(value)
      doPrintSuccess()

    case ReproducibleResourceLimit(value) =>
      regularOutputChannel(Unsupported)

    case Verbosity(value) =>
      regularOutputChannel(Unsupported)

    case AttributeOption(attribute) =>
      regularOutputChannel(Unsupported)

    case _ => ???
  }

  protected def processGetInfo(infoFlag: InfoFlag): Unit = infoFlag match {
    case AllStatisticsInfoFlag() =>
      regularOutputChannel(Unsupported)
    case AssertionStackLevelsInfoFlag() =>
      regularOutputChannel(Unsupported)
    case AuthorsInfoFlag() =>
      regularOutputChannel(Unsupported)
    case ErrorBehaviorInfoFlag() =>
      regularOutputChannel(Unsupported)
    case NameInfoFlag() =>
      regularOutputChannel(Unsupported)
    case ReasonUnknownInfoFlag() =>
      regularOutputChannel(Unsupported)
    case VersionInfoFlag() =>
      regularOutputChannel(Unsupported)
    case KeywordInfoFlag(keyword) =>
      regularOutputChannel(Unsupported)
  }

  
  private class AssertionLevel {

    var assertions: Set[Term] = Set()

    private var sortSymbols: Map[SSymbol, Int] = Map()
    private var sortAliases: Map[SSymbol, (Seq[SSymbol], Sort)] = Map()

    def isSortDefined(name: SSymbol): Boolean = 
      sortSymbols.contains(name) || sortAliases.contains(name)

    def newSortSymbol(name: SSymbol, arity: Int): Unit = {
      require(!sortSymbols.contains(name))
      sortSymbols += (name -> arity)
    }
    def newSortAlias(name: SSymbol, params: Seq[SSymbol], body: Sort): Unit = {
      require(!sortAliases.contains(name))
      sortAliases += (name -> ((params, body)))
    }


    var declareFuns: Set[DeclareFun] = Set()
    var declareConsts: Set[DeclareConst] = Set()
  }

  private var assertionStack: List[AssertionLevel] = List(new AssertionLevel)

  private def firstAssertionLevel: AssertionLevel = assertionStack.last
  private def currentAssertionLevel: AssertionLevel = assertionStack.head

  private def processPop(n: Int): Unit = {
    if(executionMode == StartMode)
      regularOutputChannel(Error("You cannot use pop in Start mode"))
    else if(assertionStack.size - n <= 0)
      regularOutputChannel(Error("You cannot pop more elements than was pushed"))
    else {
      assertionStack = assertionStack.drop(n)
      executionMode = AssertMode
      rawSolver.eval(Pop(n))
      doPrintSuccess()
    }
  }

  private def processPush(n: Int): Unit = {
    if(executionMode == StartMode)
      regularOutputChannel(Error("You cannot use push in Start mode"))
    else {
      for(i <- 1 to n)
        assertionStack ::= new AssertionLevel
      executionMode = AssertMode
      rawSolver.eval(Push(n))
      doPrintSuccess()
    }
  }

  /* check that the sort is well defined: correct arity, symbol in context.
   * TODO: how to check for built-in sorts?
   */
  def checkSort(sort: Sort, params: Seq[SSymbol]): Unit = {

  }


  def eval(command: Command): Unit = {

    if(executionMode == ExitMode) {
      regularOutputChannel(Error("The solver has exited."))
    } else {

      command match {

        case DeclareSort(name, arity) => {
          //TODO: global definitions
          if(assertionStack.exists(al => al.isSortDefined(name))) {
            regularOutputChannel(Error("Sort " + name + " already defined"))
          } else {
            currentAssertionLevel.newSortSymbol(name, arity)
            executionMode = AssertMode
            rawSolver.eval(command)
            doPrintSuccess()
          }
        }

        case DefineSort(name, params, body) => {
          //TODO: global definitions
          //TODO: check well defined sort
          if(assertionStack.exists(al => al.isSortDefined(name))) {
            regularOutputChannel(Error("Sort " + name + " already defined"))
          } else {
            currentAssertionLevel.newSortAlias(name, params, body)
            executionMode = AssertMode
            rawSolver.eval(command)
            doPrintSuccess()
          }
        }

        case GetInfo(infoFlag) => {
          processGetInfo(infoFlag)
        }

        case Exit() => {
          executionMode = ExitMode
          rawSolver.eval(command)
        }

        case Pop(n) => {
          processPop(n)
        }
        case Push(n) => {
          processPush(n)
        }

        case Reset() => {
          regularOutputChannel = onRegularOutput
          diagnosticOutputChannel = onDiagnosticOutput
          printSuccess = true
          logic = None
          globalDeclarations = false
          produceModels = false

          //TODO: if supported, else just emulate by creating a fresh instance
          rawSolver.eval(command)
        }

        case ResetAssertions() => {
          //TODO: what exactly to do with global declarations and declarations at the top level
          assertionStack = List(new AssertionLevel)
          rawSolver.eval(command)
          doPrintSuccess()
        }

        case SetLogic(log) => {
          if(executionMode != StartMode) {
            regularOutputChannel(Error("set-logic is only allowed while in Start mode"))
          } else {
            rawSolver.eval(command)
            logic = Some(log)
            executionMode = AssertMode
          }
        }

        case SetOption(option) => {
          processSetOption(option)
        }

        case _ => ???
      }

    }
  }


  //val regularOutput: Iterator[CommandResponse]

  //val diagnosticOutput: Iterator[String]

}

object SemanticsDriver {

  trait ExecutionMode
  case object StartMode extends ExecutionMode
  case object AssertMode extends ExecutionMode
  case object SatMode extends ExecutionMode
  case object UnsatMode extends ExecutionMode
  case object ExitMode extends ExecutionMode

}
