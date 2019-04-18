/* scala-stm - (c) 2009-2010, Stanford University, PPL */

package scala.concurrent.stm
package examples

/** See http://en.wikipedia.org/wiki/Dining_philosophers_problem
 *  The STM solution is particularly straightforward because we can
 *  simultaneously pick up two forks.
 */
object DiningPhilosophers {

  class Fork {
    val inUse = Ref(false)
  }

  class PhilosopherThread(meals: Int, left: Fork, right: Fork) extends Thread {
    override def run() {
      for (m <- 0 until meals) {
        // THINK
        pickUpBothForks()
        // EAT
        putDown(left)
        putDown(right)
      }
    }

    def pickUpBothForks() {
      atomic { implicit txn =>
        if (left.inUse() || right.inUse())
          retry
        left.inUse() = true
        right.inUse() = true
      }
    }

    def putDown(f: Fork) {
      f.inUse.single() = false
    }
  }

  def time(tableSize: Int, meals: Int): Long = {
    val forks = Array.tabulate(tableSize) { _ => new Fork }
    val threads = Array.tabulate(tableSize) { i => new PhilosopherThread(meals, forks(i), forks((i + 1) % tableSize)) }
    val start = System.currentTimeMillis
    for (t <- threads) t.start()
    for (t <- threads) t.join()
    System.currentTimeMillis - start
  }

  def main(args: Array[String]) {
    val meals = 100000
    for (p <- 0 until 3) {
      val elapsed = time(5, meals)
      printf("%3.1f usec/meal\n", (elapsed * 1000.0) / meals)
    }
  }
}
