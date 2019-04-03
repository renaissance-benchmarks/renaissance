package org.renaissance

import java.util.regex.Pattern
import scala.util.Failure
import scala.util.Success
import scala.util.Try

trait RenaissanceBenchmark {
  final def name: String = {
    val nameOfClass = this.getClass.getSimpleName
    val camelCaseName = if (nameOfClass.last == '$') nameOfClass.init else nameOfClass
    val pattern = Pattern.compile("([A-Za-z])([A-Z])")
    pattern.matcher(camelCaseName).replaceAll("$1-$2").toLowerCase
  }

  final def mainGroup: String = {
    val fullName = getClass.getName
    val simpleName = getClass.getSimpleName
    val packageName = fullName.substring(0, fullName.indexOf(simpleName)).init
    val groupName = packageName.substring(packageName.lastIndexOf('.') + 1)
    groupName
  }

  def defaultRepetitions = 20

  def description: String

  def initialRelease: Option[String] = None

  def finalRelease: Option[String] = None

  protected def setUpBeforeAll(c: Config) = {}

  protected def tearDownAfterAll(c: Config) = {}

  protected def beforeIteration(c: Config) = {}

  protected def afterIteration(c: Config) = {}

  final def runBenchmark(config: Config): Try[Unit] = {
    try {
      setUpBeforeAll(config)
      val factory = Policy.factories.getOrElse(config.policy, sys.error("Unknown policy."))
      val policy = factory.apply(this, config)
      for (plugin <- config.plugins) plugin.onStart(policy)
      try policy.execute()
      finally for (plugin <- config.plugins) plugin.onTermination(policy)
    } catch {
      case t: Throwable =>
        return Failure(t)
    } finally {
      tearDownAfterAll(config)
    }
  }

  protected def runIteration(config: Config): Unit

  def runIterationWithBeforeAndAfter(policy: Policy, config: Config): Long = {
    beforeIteration(config)

    for (plugin <- config.plugins) plugin.beforeIteration(policy)

    val start = System.nanoTime

    runIteration(config)

    val end = System.nanoTime
    val duration = end - start

    for (plugin <- config.plugins) plugin.afterIteration(policy, duration)

    afterIteration(config)

    duration
  }
}

case class Config(
  val benchmarkList: Seq[String] = Seq(),
  val repetitions: Int = -1,
  val plugins: Seq[Plugin] = Seq(),
  val policy: String = "fixed",
  val readme: Boolean = false
) {

  def withBenchmarkSpecification(v: String): Config =
    this.copy(benchmarkList = v.split(",").toSeq)

  def withPlugins(v: String): Config = {
    val pluginNames = v.split(",")
    val plugins = for (name <- pluginNames) yield {
      Class.forName(name).newInstance().asInstanceOf[Plugin]
    }
    this.copy(plugins = plugins)
  }
}

/** Base class for plugins that gather other metrics.
 *
 *  Subclasses must have a zero arguments constructor.
 */
trait Plugin {

  /** Called once after the plugin is created.
   */
  def onCreation(): Unit

  /** Called before a benchmark starts executing.
   */
  def onStart(policy: Policy): Unit = {}

  def beforeIteration(policy: Policy): Unit

  def afterIteration(policy: Policy, duration: Long): Unit

  /** Called after the benchmark is done executing.
   */
  def onTermination(policy: Policy): Unit = {}

  /** Called once after all benchmarks are done executing.
   */
  def onExit(): Unit = {}
}

/** The policy that executes the benchmark
 */
sealed trait Policy {
  def description: String

  /** The name of the benchmark that is currently executing.
   */
  def currentBenchmarkName: String = currentBenchmark.name

  /** The benchmark that is executing.
   */
  private[renaissance] def currentBenchmark: RenaissanceBenchmark

  /** Runs the benchmark multiple times.
   */
  private[renaissance] def execute(): Try[Unit]
}

object Policy {

  val factories = Map[String, (RenaissanceBenchmark, Config) => Policy](
    "fixed" -> { (benchmark, config) =>
      new FixedIterationsPolicy(benchmark, config)
    }
  )

  def descriptions: Map[String, String] = factories.map {
    case (name, factory) =>
      val policy = factory(new Dummy, new Config)
      (name, policy.description)
  }
}

/** Represents a run in which a fixed number of iterations are sequentially executed.
 */
final class FixedIterationsPolicy(
  private[renaissance] val currentBenchmark: RenaissanceBenchmark,
  private val config: Config
) extends Policy {
  private var iteration = 0

  val totalIterations: Int =
    if (config.repetitions < 0) currentBenchmark.defaultRepetitions else config.repetitions

  def description = "Runs the benchmark for a fixed number of iterations."

  /** The current iteration.
   */
  def currentIteration: Int = iteration

  private[renaissance] def execute(): Try[Unit] = {
    while (iteration < totalIterations) {
      val name = currentBenchmark.name
      val g = currentBenchmark.mainGroup
      if (iteration == totalIterations - 1) {
        println(s"====== $name ($g), final iteration started ======")
      } else {
        println(s"====== $name ($g), iteration $iteration started ======")
      }
      val nanos = currentBenchmark.runIterationWithBeforeAndAfter(this, config)
      val millis = (nanos / 1000).toInt / 1000.0
      if (iteration == totalIterations - 1) {
        println(s"====== $name ($g), final iteration completed ($millis ms) ======")
      } else {
        println(s"====== $name ($g), iteration $iteration completed ($millis ms) ======")
      }
      iteration += 1
    }
    Success(())
  }
}

final class Dummy extends RenaissanceBenchmark {
  override def description: String = "A dummy benchmark, which does no work."

  protected override def runIteration(config: Config): Unit = {}
}
