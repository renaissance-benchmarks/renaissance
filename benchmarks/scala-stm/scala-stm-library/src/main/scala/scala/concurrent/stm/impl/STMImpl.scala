/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm
package impl

import java.util.concurrent.TimeUnit

private[impl] object STMImplHolder {
  var instance: STMImpl = STMImpl.createInstance()
}

/** `STMImpl` gathers all of the functionality required to plug an STM
 *  implementation into `scala.concurrent.stm`.  Only one implementation can
 *  be selected, because `Ref`s and atomic blocks from different STM
 *  implementations are not compatible.  `STMImpl.instance` returns the
 *  `STMImpl` instance that has been selected for this program execution.
 *
 *  There are two ways to explicitly select the `STMImpl` instance:
 *
 *  1. set the JVM system property "scala.stm.impl" to the name of a class
 *     that implements `STMImpl`; or
 *
 *  2. arrange for `STMImpl.select` or `STMImpl.trySelect` to be called
 *     before any `Ref`s are constructed and before any atomic blocks are
 *     executed.
 *
 *  Setting the JVM system property "scala.stm.impl" is equivalent to making a
 *  call to `STMImpl.select(System.getProperty("scala.stm.impl"))` before any
 *  other `STMImpl` selections.
 *
 *  If there is no explicitly selected `STMImpl` instance and the classpath
 *  contains a class `scala.concurrent.stm.impl.DefaultFactory` that extends
 *  `scala.concurrent.stm.impl.STMImpl.Factory`, then an instance of that
 *  class will be instantiated and used to generate the `STMImpl` instance.
 *  ScalaSTM implementations are encouraged to implement `DefaultFactory` so
 *  that if a user includes the implementation's JAR file, it will be
 *  automatically selected.
 *
 *  If no explicit selection has been made and there is no definition of
 *  `scala.concurrent.stm.impl.DefaultFactory` present in the classpath, then
 *  ScalaSTM will fall back to the reference implementation
 *  "scala.concurrent.stm.ccstm.CCSTM".
 *
 *  @author Nathan Bronson
 */
object STMImpl {
  trait Factory {
    def createInstance(): STMImpl
  }

  /** Returns the instance of `STMImpl` that should be used to implement all
   *  ScalaSTM functionality.  Calling this method forces the implementation
   *  to be chosen if it has not already been selected.
   */
  def instance: STMImpl = STMImplHolder.instance

  // We duplicate the implementation of select() to avoid the need to
  // instantiate an STM that we won't end up using

  /** If no `STMImpl` instance has yet been selected, installs an instance of
   *  `Class.forName(implClassName)` as the system-wide STM implementation.
   *  Returns true if `implClassName` was newly or previously selected, or
   *  returns false if another STM implementation was chosen.
   */
  def trySelect(implClassName: String): Boolean = {
    explicitChoice = implClassName
    instance.getClass.getName == implClassName
  }

  /** Installs `Class.forName(implClassName)` as the system-wide STM
   *  implementation if no `STMImpl` has yet been chosen, or verifies that
   *  `implClassName` was previously selected, throwing 
   *  `IllegalStateException` if a different STM implementation has already
   *  been selected
   */
  def select(implClassName: String) {
    if (!trySelect(implClassName)) {
      throw new IllegalStateException(
          "unable to select STMImpl class " + implClassName + ", " + instance + " already installed");
    }
  }

  /** Installs `impl` as the system-wide STM implementation if no `STMImpl`
   *  has yet been chosen, or verifies that `impl` is equal to the previously
   *  selected instance, throwing `IllegalStateException` if an STM
   *  implementation has already been selected and `impl != instance`
   */
  def select(impl: STMImpl) {
    explicitChoice = impl
    if (impl != instance) {
      throw new IllegalStateException(
          "unable to select STMImpl " + impl + ", " + instance + " already installed");
    }
  }


  /** May be a String class name, an STMImpl, or null */
  @volatile private var explicitChoice: AnyRef = null

  private[impl] def createInstance(): STMImpl = {
    var choice: AnyRef = System.getProperty("scala.stm.impl")

    if (choice == null)
      choice = explicitChoice

    if (choice == null) {
      choice = (try {
        val fc = Class.forName("scala.concurrent.stm.impl.DefaultFactory")
        fc.newInstance().asInstanceOf[STMImpl.Factory].createInstance()
      } catch {
        case _: ClassNotFoundException => "scala.concurrent.stm.ccstm.CCSTM"
      })
    }

    choice match {
      case s: String => Class.forName(s).newInstance().asInstanceOf[STMImpl]
      case i: STMImpl => i
    }
  }
}

/** `STMImpl` gathers all of the functionality required to plug an STM
 *  implementation into `scala.concurrent.stm`.  See the `STMImpl` companion
 *  object for information on controlling which `STMImpl` is selected at run
 *  time.
 *
 *  @author Nathan Bronson
 */
trait STMImpl extends RefFactory with TxnContext with TxnExecutor {

  /** Returns a new commit barrier suitable for coordinating commits by this
   *  STM implementation.
   */
  def newCommitBarrier(timeout: Long, unit: TimeUnit): CommitBarrier
}
