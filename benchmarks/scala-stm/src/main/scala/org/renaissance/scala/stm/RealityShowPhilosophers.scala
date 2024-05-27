package org.renaissance.scala.stm

import scala.annotation.tailrec
import scala.collection.mutable
import scala.concurrent.stm.atomic
import scala.concurrent.stm.retry
import scala.concurrent.stm.Ref

/**
 * This extends a solution to the dining philosopher's problem to include an
 * outside perspective that periodically examines what is happening.
 */
object RealityShowPhilosophers {

  private class Fork(val name: String) {
    private[stm] val owner = Ref(None: Option[String])
  }

  private class PhilosopherThread(
    val name: String,
    val meals: Int,
    left: Fork,
    right: Fork
  ) extends Thread {
    private[stm] val mealsEaten = Ref(0)

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
  }

  private class CameraThread(
    intervalMilli: Int,
    forks: Seq[Fork],
    philosophers: Seq[PhilosopherThread]
  ) extends Thread {
    private[stm] val images = mutable.Buffer[String]()

    @tailrec final override def run(): Unit = {
      Thread.sleep(intervalMilli)
      val (image, done) = captureImage
      images += image
      if (!done) {
        run()
      } else {
        // TODO Consistent way of handling stdout.
        //  See https://github.com/D-iii-S/renaissance-benchmarks/issues/20
        println(s"Camera thread performed ${images.length} scans.")
      }
    }

    private def captureImage: (String, Boolean) =
      //
      // We want to capture exactly one image of the final state, so we
      // check completion at the same time as building the image.
      //
      atomic { implicit txn =>
        val image = new StringBuilder
        for (f <- forks)
          image ++= "%s is owned by %s\n".format(f.name, f.owner.single())

        var done = true
        for (p <- philosophers) {
          val progress = p.mealsEaten.single() * 100.0 / p.meals
          image ++= "%s is %5.2f%% done\n".format(p.name, progress)
          done &&= p.done
        }

        (image.toString, done)
      }
  }

  def run(mealCount: Int, philosopherCount: Int): (Seq[Option[String]], Seq[Int]) = {
    val forks = Array.tabulate(philosopherCount) { i => new Fork(s"fork-$i") }
    val philosophers = Array.tabulate(philosopherCount) { i =>
      new PhilosopherThread(
        s"philosopher-$i",
        mealCount,
        forks(i),
        forks((i + 1) % forks.length)
      )
    }

    val camera = new CameraThread(1000 / 60, forks, philosophers)

    camera.start()
    philosophers.foreach(_.start())
    philosophers.foreach(_.join())
    camera.join()

    // Collect fork owners and meals eaten for validation.
    atomic { implicit txn =>
      (forks.map(_.owner.get), philosophers.map(_.mealsEaten.get))
    }
  }
}
