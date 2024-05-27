package org.renaissance.scala.stm

import java.util.concurrent.LinkedBlockingDeque

import scala.collection.mutable
import scala.concurrent.stm.atomic
import scala.concurrent.stm.retry
import scala.concurrent.stm.Ref

/**
 * This extends a solution to the dining philosopher's problem to include an
 * outside perspective that periodically examines what is happening.
 */
object RealityShowPhilosophers {

  /**
   * Issues quasi-periodic requests to snapshot the state of the system.
   * Instead of regular wall-clock intervals, the requests are triggered
   * when certain progress has been made (measured with coarse granularity).
   *
   * The requests are queued to prevent potential loss of wake-ups due to
   * increasing rate of progress (with decreasing contention). This also
   * ensures a constant number of "camera scans" in the workload.
   */
  private class CameraController(blockDivider: Int) {
    private val blockMask = (1 << 12) - 1
    private val blockCount = Ref(0)
    private val requests = new LinkedBlockingDeque[Option[Thread]]

    def reportProgress(mealsEaten: Int): Unit = {
      if ((mealsEaten & blockMask) != 0) {
        return
      }

      // Determine whether to issue a request.
      val issueRequest = atomic { implicit txn =>
        val newBlockCount = blockCount.transformAndGet(_ + 1)
        (newBlockCount % blockDivider) == 0
      }

      // Issue the request if necessary.
      if (issueRequest) {
        requests.put(Some(Thread.currentThread()))
      }
    }

    def shutdown(): Unit = {
      // Issue an empty request to signal shutdown.
      requests.put(None)
    }

    def awaitRequest(): Option[Thread] = {
      // Dequeue a request from the queue.
      requests.take()
    }
  }

  private class Fork(val name: String) {
    private[stm] val owner = Ref(None: Option[String])
  }

  private class PhilosopherThread(
    val name: String,
    val meals: Int,
    left: Fork,
    right: Fork,
    controller: CameraController
  ) extends Thread {
    private[stm] val mealsEaten = Ref(0)

    override def run(): Unit = {
      val self = Some(name)

      for (_ <- 0 until meals) {
        // Thinking.
        atomic { implicit txn =>
          if (!(left.owner().isEmpty && right.owner().isEmpty)) {
            retry
          }

          left.owner() = self
          right.owner() = self
        }

        // Eating.
        val newMealsEaten = atomic { implicit txn =>
          left.owner() = None
          right.owner() = None
          mealsEaten.transformAndGet(_ + 1)
        }

        controller.reportProgress(newMealsEaten)
      }
    }
  }

  private class CameraThread(
    forks: Seq[Fork],
    philosophers: Seq[PhilosopherThread],
    controller: CameraController
  ) extends Thread {
    private[stm] val images = mutable.Buffer[String]()

    final override def run(): Unit = {
      // Captures "image" of the show's state when requested.
      // Finish execution upon receiving an empty request.
      while (controller.awaitRequest().isDefined) {
        // Separate state snapshot from rendering.
        val (forkOwners, mealsEaten) = stateSnapshot
        images += renderImage(forkOwners, mealsEaten)
      }

      // TODO Consistent way of handling stdout.
      //  See https://github.com/D-iii-S/renaissance-benchmarks/issues/20
      println(s"Camera thread performed ${images.length} scans.")
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
  }

  def run(mealCount: Int, philosopherCount: Int): (Seq[Option[String]], Seq[Int]) = {
    val forks = Array.tabulate(philosopherCount) { i => new Fork(s"fork-$i") }
    val controller = new CameraController(philosopherCount)
    val philosophers = Array.tabulate(philosopherCount) { i =>
      new PhilosopherThread(
        s"philosopher-$i",
        mealCount,
        forks(i),
        forks((i + 1) % forks.length),
        controller
      )
    }

    val camera = new CameraThread(forks, philosophers, controller)

    camera.start()
    philosophers.foreach(_.start())
    philosophers.foreach(_.join())

    // Signal shutdown to the camera after the philosophers finish.
    controller.shutdown()
    camera.join()

    // Collect fork owners and meals eaten for validation.
    camera.stateSnapshot
  }
}
