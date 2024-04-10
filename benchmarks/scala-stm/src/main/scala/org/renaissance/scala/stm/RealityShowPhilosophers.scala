package org.renaissance.scala.stm

import scala.annotation.tailrec
import scala.collection._
import scala.concurrent.stm._

/**
 * This extends a solution to the dining philosopher's problem to include an
 * outside perspective that occasionally examines everything that is
 * happening.
 */
object RealityShowPhilosophers {

  class Fork {
    val owner = Ref(None: Option[String])
  }

  class PhilosopherThread(
    val name: String,
    val meals: Int,
    left: Fork,
    right: Fork
  ) extends Thread {
    val mealsEaten = Ref(0)

    override def run(): Unit = {
      for (_ <- 0 until meals) {
        // Thinking.
        atomic { implicit txn =>
          if (!(left.owner().isEmpty && right.owner().isEmpty))
            retry
          left.owner() = Some(name)
          right.owner() = Some(name)
        }
        // Eating.
        atomic { implicit txn =>
          mealsEaten += 1
          left.owner() = None
          right.owner() = None
        }
      }
    }

    def done: Boolean = mealsEaten.single() == meals

    override def toString: String =
      "%s is %5.2f%% done".format(name, mealsEaten.single() * 100.0 / meals)
  }

  class CameraThread(
    intervalMilli: Int,
    forks: Seq[Fork],
    philosophers: Seq[PhilosopherThread]
  ) extends Thread {
    val outputs = mutable.Buffer[String]()

    @tailrec final override def run(): Unit = {
      Thread.sleep(intervalMilli)
      val (str, done) = image
      outputs += str
      if (!done) {
        run()
      } else {
        // TODO Consistent way of handling stdout.
        //  See https://github.com/D-iii-S/renaissance-benchmarks/issues/20
        println(s"Camera thread performed ${outputs.length} scans.")
      }
    }

    /**
     * We want to print exactly one image of the final state, so we check
     * completion at the same time as building the image.
     */
    def image: (String, Boolean) =
      atomic { implicit txn =>
        val buf = new StringBuilder
        for (i <- forks.indices)
          buf ++= "fork %d is owned by %s\n".format(i, forks(i).owner.single())
        var done = true
        for (p <- philosophers) {
          buf ++= p.toString += '\n'
          done &&= p.done
        }
        (buf.toString, done)
      }
  }

  def eatenMeals(philosopherCount: Int, meals: Int): Array[Int] = {
    val names = for (i <- 0 until philosopherCount) yield {
      s"philosopher-$i"
    }
    val forks = Array.tabulate(names.size) { _ =>
      new Fork
    }
    val pthreads = Array.tabulate(names.size) { i =>
      new PhilosopherThread(names(i), meals, forks(i), forks((i + 1) % forks.length))
    }
    val camera = new CameraThread(1000 / 60, forks, pthreads)
    camera.start()
    for (t <- pthreads) t.start()
    for (t <- pthreads) t.join()
    camera.join()
    atomic { implicit txn =>
      pthreads.map { p =>
        p.mealsEaten.get(txn)
      }
    }
  }

  def run(meals: Int, philosopherCount: Int) = {
    eatenMeals(philosopherCount, meals)
  }
}
