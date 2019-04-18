/* scala-stm - (c) 2009-2011, Stanford University, PPL */

package scala.concurrent.stm
package examples

import annotation.tailrec

/** This extends a solution to the dining philosopher's problem to include an
 *  outside perspective that occasionally examines everything that is
 *  happening.
 */
object RealityShowPhilosophers {

  class Fork {
    val owner = Ref(None : Option[String])
  }

  class PhilosopherThread(val name: String, val meals: Int, left: Fork, right: Fork) extends Thread {
    val mealsEaten = Ref(0)

    override def run() {
      for (m <- 0 until meals) {
        // thinking
        atomic { implicit txn =>
          if (!(left.owner().isEmpty && right.owner().isEmpty))
            retry
          left.owner() = Some(name)
          right.owner() = Some(name)
        }
        // eating
        atomic { implicit txn =>
          mealsEaten += 1
          left.owner() = None
          right.owner() = None
        }
      }
    }

    def done = mealsEaten.single() == meals

    override def toString = {
      "%s is %5.2f%% done".format(name, mealsEaten.single() * 100.0 / meals)
    }
  }

  class CameraThread(intervalMilli: Int, forks: Seq[Fork], philosophers: Seq[PhilosopherThread]) extends Thread {

    @tailrec final override def run() {
      Thread.sleep(intervalMilli)
      val (str, done) = image
      println(str)
      if (!done)
        run()
    }

    /** We want to print exactly one image of the final state, so we check
     *  completion at the same time as building the image.
     */
    def image: (String, Boolean) = atomic { implicit txn =>
      val buf = new StringBuilder
      for (i <- 0 until forks.length)
        buf ++= "fork %d is owned by %s\n".format(i, forks(i).owner.single())
      var done = true
      for (p <- philosophers) {
        buf ++= p.toString += '\n'
        done &&= p.done
      }
      (buf.toString, done)
    }
  }

  def time(names: Seq[String], meals: Int): Long = {
    val forks = Array.tabulate(names.size) { _ => new Fork }
    val pthreads = Array.tabulate(names.size) { i => new PhilosopherThread(names(i), meals, forks(i), forks((i + 1) % forks.length)) }
    val camera = new CameraThread(1000 / 60, forks, pthreads)
    val start = System.currentTimeMillis
    camera.start()
    for (t <- pthreads) t.start()
    for (t <- pthreads) t.join()
    val elapsed = System.currentTimeMillis - start
    camera.join()
    elapsed
  }

  def main(args: Array[String]) {
    val meals = 100000
    for (p <- 0 until 3) {
      val elapsed = time(List("Aristotle", "Hippocrates", "Plato", "Pythagoras", "Socrates"), meals)
      printf("%3.1f usec/meal\n", (elapsed * 1000.0) / meals)
    }
  }
}
