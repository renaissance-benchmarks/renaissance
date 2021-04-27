package cafesat

import java.io.File

import util._

object Main {

  object FileFormat extends Enumeration {
    type FileFormat = Value
    val Dimacs, SmtLib  = Value
  }
  import FileFormat._

  private var fileFormat: FileFormat = Dimacs

  private var time = false

  private val optionsHelp: String = (
    "  --format=[dimacs|smtlib2]     The input file format (default: dimacs)" + "\n" +
    "  --engine=[dpllt|blackbox]     The engine to use for the boolean exploration" + "\n" +
    "  --strategy=[lazy|eager]       The strategy for communication with theory solvers" + "\n" +
    "  --solvers=s1,s2,...           Specify particular theory solver implementation to use instead of standard ones" + "\n" +

    "  --loglevel=[1-5]              Log level, 1 for tracing and 5 for error only (default: 4, warnings)" + "\n" +
    "  --tags=t1:...                 Filter out debug information that are not of one of the given tags" + "\n" +
    "  --timeout=N                   Timeout in seconds" + "\n" +

    "  --stats                       Print statistics information" + "\n" +

    "  --restartfactor=N             Restart strategy factor" + "\n" +
    "  --restartinterval=N           Restart strategy initial interval" + "\n" +
    //"  --no-print-success   Desactivate the :print-success default option of SMT-LIB standard" + "\n"

    "  --time                        Time the solving phase"
  )

  def processOptions(options: Array[String]): Unit = {
    for(option <- options) {
      option match {
        //TODO: we should use a --format=[dimacs|smtlib2] instead
        case "dimacs" =>                                  fileFormat = Dimacs
        case "smtlib2" | "smtlib" =>                      fileFormat = SmtLib
        case "time"        =>                             time = true
        //case "no-print-success"    =>                     Settings.printSuccess = Some(false)

        case "stats" =>                                   Settings.stats = true

        case "verbose" =>                                 Settings.logLevel = Logger.Debug
        case "trace" =>                                   Settings.logLevel = Logger.Trace


        case s if s.startsWith("engine=") => s.substring("engine=".length) match {
          case "dpllt" => Settings.engine = Settings.DPLLT
          case "blackbox" => Settings.engine = Settings.BlackBox
          case _ => Settings.engine = Settings.DPLLT
        }

        case s if s.startsWith("loglevel=") => Settings.logLevel = try {
          s.substring("loglevel=".length).toInt match {
            case 1 => Logger.Trace
            case 2 => Logger.Debug
            case 3 => Logger.Info
            case 4 => Logger.Warning
            case 5 => Logger.Error
          }
        } catch {
          case (_: Throwable) => Logger.Warning
        }

        //case s if s.startsWith("tags=") =>                Settings.debugTags = Set(splitList(s.substring("tags=".length, s.length)): _*)
        case s if s.startsWith("timeout=") =>             Settings.timeout = try { 
                                                            Some(s.substring("timeout=".length, s.length).toInt)
                                                          } catch { 
                                                            case (_: Throwable) => None
                                                          }
        case s if s.startsWith("restartinterval=") =>     try { 
                                                            Settings.restartInterval = s.substring("restartInterval=".length, s.length).toInt
                                                          } catch { 
                                                            case (_: Throwable) =>
                                                          }
        case s if s.startsWith("restartfactor=") =>       try { 
                                                            Settings.restartFactor = s.substring("restartFactor=".length, s.length).toDouble
                                                          } catch { 
                                                            case (_: Throwable) =>
                                                          }
        case _ => //Reporter.error("Invalid option: " + option + "\nValid options are:\n" + optionsHelp)
      }
    }
  }

  import sat.Solver
  import Solver.Results._

  //use the SAT solver to solve a Dimacs file. The option
  //useDPLLT controls whether we use the raw SAT solver (false) or
  //the DPLLT with abstract theory solver instantiated by a PropositionalSolver.
  //Ideally both should be as fast, but so far there seems to be a lot of overhead
  //to use DPLLT.
  private def satSolver(f: File, useDPLLT: Boolean = false)(implicit context: Context) = {
    val input = new java.io.FileReader(f)
    val (satInstance, nbVars) = parsers.Dimacs.cnf(input)
    if(useDPLLT) {
      val s = new dpllt.DPLLSolver[dpllt.BooleanTheory.type](nbVars, dpllt.BooleanTheory)
      val cnf = satInstance.map(clause => {
        val lits: Set[s.theory.Literal] =
          clause.map(l => dpllt.BooleanTheory.PropositionalLiteral(l.getID, if(l.polarity) 1 else 0))
        lits
      }).toSet
      cnf.foreach(lits => s.addClause(lits))
      val res = s.solve(dpllt.BooleanTheory.makeSolver(cnf))
      res match {
        case dpllt.DPLLSolver.Results.Satisfiable(_) => println("sat")
        case dpllt.DPLLSolver.Results.Unsatisfiable => println("unsat")
        case dpllt.DPLLSolver.Results.Unknown => println("unknown")
      }
      res
    } else {
      val s = new Solver(nbVars)
      satInstance.foreach(s.addClause(_))
      val res = s.solve()
      res match {
        case Satisfiable(_) => println("sat")
        case Unsatisfiable => println("unsat")
        case Unknown => println("unknown")
      }
      res
    }
  }



  def main(arguments: Array[String]): Unit = {
    try {
      val (options0, trueArgs) = arguments.partition(str => str.startsWith("--"))
      val options = options0.map(str => str.substring(2))
      processOptions(options)

      val logger = Settings.logLevel match {
        case Logger.Error => ErrorStdErrLogger
        case Logger.Warning => DefaultStdErrLogger
        case Logger.Info => InfoStdErrLogger
        case Logger.Debug => VerboseStdErrLogger
        case Logger.Trace => TraceStdErrLogger
        case _ => DefaultStdErrLogger
      }
      implicit val context = Context(logger = logger)

      //TODO: provide a REPL
      //if(trueArgs.size == 0) {
      //  val repl = new regolic.smtlib.REPL
      //  repl.run
      //}

      val inputFile = trueArgs(0)
      val start = System.currentTimeMillis
      fileFormat match {
        case Dimacs =>
          val useDPLLT = Settings.engine == Settings.DPLLT
          satSolver(new java.io.File(inputFile), useDPLLT)
        case SmtLib =>
          println("smtlib format not yet supported")
          sys.exit(0)
      }
      val end = System.currentTimeMillis
      val elapsed = end - start
      if(time)
        println(elapsed/1000d)
      sys.exit(0)
    } catch {
      case (e: Throwable) =>
        e.printStackTrace
        sys.exit(1)
    }
  }

  private def recursiveListFiles(f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter(_.isDirectory).flatMap(recursiveListFiles)
  }

}
