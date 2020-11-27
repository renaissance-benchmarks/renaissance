package smtlib

/** provides drivers that adapt standard SMT-LIB to solver specific behaviour
  *
  * In particula, some solvers only support a subset of SMT-LIB or an outdated
  * version. The aim of the drivers are to simplify the interface for other tools.
  * All the tools have to be concerned about is to follow the SMT-LIB standard, and
  * the driver will take care of any peculiarity of the solver.
  */
package object drivers {

}
