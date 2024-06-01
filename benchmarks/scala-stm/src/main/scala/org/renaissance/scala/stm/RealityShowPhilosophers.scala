package org.renaissance.scala.stm

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
   * Issues quasi-periodic requests to snapshot the state of the "show".
   * Instead of regular wall-clock intervals, the requests are triggered
   * when certain progress has been made (measured with coarse granularity).
   *
   * The requests are counted to prevent potential loss of wake-ups due to
   * increasing rate of progress (with decreasing contention). This ensures
   * a constant number of "camera scans" in the workload.
   */
  private final class CameraController(philosopherCount: Int, blockMealCount: Int) {

    /** Mask to simplify block completion checks. Requires [[blockMealCount]] to be a power of 2. */
    private val blockMask = blockMealCount - 1

    private val blockCount = Ref(0)
    private val requestCount = Ref(0)
    private val scanCount = Ref(0)
    private val terminate = Ref(false)

    /** @return `true` if the current progress amounts to a complete block, `false` otherwise. */
    def isBlockComplete(mealsEaten: Int): Boolean = (mealsEaten & blockMask) == 0

    /**
     * Notifies the controller that a block of progress has been made.
     * Triggers a camera scan when enough blocks have been reported.
     */
    def notifyBlockComplete(): Unit = {
      atomic { implicit txn =>
        val newBlockCount = blockCount.transformAndGet(_ + 1)
        if ((newBlockCount % philosopherCount) == 0) {
          requestCount += 1
        }
      }
    }

    /**
     * Instructs the controller to signal termination when the number of scans
     * performed reaches the number of scans requested.
     */
    def shutdown(): Unit = {
      terminate.single() = true
    }

    /**
     * Waits for a camera "scan" request, unless the number of scans performed
     * reached the total (fixed) number of scans to be performed in the workload.
     *
     * @return scan request index (non-negative), `-1` to indicate termination.
     */
    def awaitRequest(): Int = {
      atomic { implicit txn =>
        if (scanCount() < requestCount()) {
          scanCount.getAndTransform(_ + 1)
        } else if (terminate()) {
          // Signal end of processing.
          -1
        } else {
          retry
        }
      }
    }
  }

  private final class Fork(val name: String) {
    private[stm] val owner = Ref(None: Option[String])
  }

  private final class PhilosopherThread(
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

        if (controller.isBlockComplete(newMealsEaten)) {
          controller.notifyBlockComplete()
        }
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
      while (controller.awaitRequest() >= 0) {
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

  def run(
    mealCount: Int,
    philosopherCount: Int,
    blockMealCount: Int
  ): (Seq[Option[String]], Seq[Int], Int) = {
    val forks = Array.tabulate(philosopherCount) { i => new Fork(s"fork-$i") }
    val controller = new CameraController(philosopherCount, blockMealCount)
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
    val (forkOwners, mealsEaten) = camera.stateSnapshot
    (forkOwners, mealsEaten, camera.images.length)
  }
}
