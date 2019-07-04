package cafesat

import util.Logger

object Settings {

  var stats = false

  var timeout: Option[Int] = None

  var restartInterval: Int = 0
  var restartFactor: Double = 1.1

  var logLevel: Logger.LogLevel = Logger.Warning

  var engine: Engine = DPLLT

  /*
   * The idea of the Engine is that there are several ways to integrate theory solvers
   * into a propositional search, the DPLLT is to generalize the SAT solver to plug-in the
   * theory solvers, while the BlackBox approach would be to keep the SAT solver independent
   * and use a different communication mecanisms (some external mapping between varID and literal
   * ids).
   */
  sealed trait Engine
  case object DPLLT extends Engine
  case object BlackBox extends Engine

  /*
   * SMT-LIB interpreter command-line/programmable options (by opposition to SMT-LIB scripting options)
   */

  //We would like to turn off :print-success for integration testing
  var printSuccess: Option[Boolean] = None //None means one should use default value of interpreter
  //tell the SMT-LIB interpreter to use the logger from context instead of default logger specified by standard
  //var useContextLogger: Boolean = false

}
