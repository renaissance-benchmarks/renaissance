import sbt.Def
import sbt.Task

import scala.collection.Seq

object Tasks {

  /**
   * Collects results from a sequence of tasks. This cannot be done using
   * a simple map over the tasks, because 'value' is a macro that captures
   * task dependency and cannot be used outside another task or in a lambda.
   * Instead, we recursively build a tree of dependent tasks in a way that
   * allows SBT to track the task dependencies. The resulting task tree also
   * allows the leaf tasks to be evaluated in parallel.
   */
  def collect[A](tasks: Seq[Def.Initialize[Task[A]]]): Def.Initialize[Task[Seq[A]]] = {
    tasks match {
      // Special cases for up to 3 tasks.
      case Nil => Def.task { Nil }
      case x :: Nil => Def.task { Seq(x.value) }
      case x :: y :: Nil => Def.task { Seq(x.value) :+ y.value }
      case x :: y :: z :: Nil => Def.task { Seq(x.value) :+ y.value :+ z.value }
      // Recursively split task list until hitting a special case.
      case _ =>
        val (xs, ys) = tasks.splitAt(tasks.length / 2)
        Def.task { collect(xs).value ++ collect(ys).value }
    }
  }

  /**
   * This is a variant of [[collect]] that evaluates tasks sequentially
   * by organizing them in a degenerated tree and using the task 'map'
   * method to wait for task value. This is what SBT sequential task
   * does, except we collect all task values instead of just the last.
   */
  def collectSequentially[A](
    tasks: Seq[Def.Initialize[Task[A]]]
  ): Def.Initialize[Task[Seq[A]]] =
    tasks match {
      case Nil => Def.task { Nil }
      // The combination of taskDyn and map serializes task evaluation.
      case x :: xs => Def.taskDyn { collectSequentially(xs).map(x.value +: _) }
    }

}
