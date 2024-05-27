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
      val self = Some(name)

      for (_ <- 0 until meals) {
        // Thinking.
        atomic { implicit txn =>
          if (!(left.owner().isEmpty && right.owner().isEmpty))
            retry

          left.owner() = self
          right.owner() = self
        }

        // Eating.
        atomic { implicit txn =>
          mealsEaten += 1

          left.owner() = None
          right.owner() = None
        }
      }
    }
  }

  private class CameraThread(
    intervalMilli: Int,
    forks: Seq[Fork],
    philosophers: Seq[PhilosopherThread]
  ) extends Thread {
    private[stm] val images = mutable.Buffer[String]()

    @tailrec final override def run(): Unit = {
      Thread.sleep(intervalMilli)

      // Separate state snapshot from rendering.
      val (forkOwners, mealsEaten) = stateSnapshot
      images += renderImage(forkOwners, mealsEaten)

      // Check completion to get exactly one image of final state.
      if (!showIsOver(mealsEaten)) {
        run()
      } else {
        // TODO Consistent way of handling stdout.
        //  See https://github.com/D-iii-S/renaissance-benchmarks/issues/20
        println(s"Camera thread performed ${images.length} scans.")
      }
    }

    def stateSnapshot: (Seq[Option[String]], Seq[Int]) =
      atomic { implicit txn =>
        val forkOwners = forks.map(_.owner.get)
        val mealsEaten = philosophers.map(_.mealsEaten.get)
        (forkOwners, mealsEaten)
      }

    private def renderImage(forkOwners: Seq[Option[String]], mealsEaten: Seq[Int]): String = {
      val image = new StringBuilder

      forks.zip(forkOwners).foreach {
        case (f, owner) =>
          image ++= "%s is owned by %s\n".format(f.name, owner)
      }

      philosophers.zip(mealsEaten).foreach {
        case (p, eaten) =>
          image ++= "%s is %5.2f%% done\n".format(p.name, eaten * 100.0 / p.meals)
      }

      image.toString()
    }

    private def showIsOver(mealsEaten: Seq[Int]): Boolean =
      philosophers.zip(mealsEaten).forall { case (p, eaten) => p.meals == eaten }

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
    camera.stateSnapshot
  }
}
