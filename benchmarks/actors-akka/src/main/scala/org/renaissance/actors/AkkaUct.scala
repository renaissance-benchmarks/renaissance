package org.renaissance.actors

import akka.actor.ActorSystem
import akka.actor.Props

import java.util.Random

import org.renaissance.Benchmark
import org.renaissance.Benchmark.*
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.ValidationException
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

import scala.concurrent.Await
import scala.concurrent.Promise
import scala.concurrent.duration.Duration

/**
 * Akka implementation of the Unbalanced Cobwebbed Tree (UCT) actor workload.
 *
 * Based on the UCT benchmark from the Savina actor benchmark suite (Imam and Sarkar,
 * AGERE! 2014); reworked for Renaissance to add a validatable computation.
 *
 * Every node holds a temperature. When a temperature reading is requested across the
 * UCT, the interior nodes average the readings of their children while the leaves report
 * fixed values derived from the node ID.
 *
 * During the final request, the root sends [[MeasureTemperatureMessage]] to every child
 * and [[UrgentUpdateTemperatureMessage]] (a [[akka.dispatch.ControlMessage]]) to each
 * urgent child. The priority mailbox delivers the update first at every hop, so urgent
 * leaves report their updated temperature within the same reduction.
 *
 * Multiple urgent paths are supported: the topology carries a set of urgent root-to-leaf
 * paths selected by [[UctUrgentPathSelector]], all of which are updated simultaneously
 * during the final request.
 *
 * The expected root temperature is computed analytically as the bottom-up average over
 * all leaves with every urgent leaf fixed at the per-topology shock temperature
 * derived from urgent leaf depths (see [[AkkaUct.computeShockTemperature]]).
 */
@Name("akka-uct")
@Group("actors")
@Group("concurrency")
@Summary("Runs the Unbalanced Cobwebbed Tree actor workload in Akka.")
@Licenses(Array(License.MIT))
@Repetitions(24)
@Parameter(
  name = "node_count_max",
  defaultValue = "200000",
  summary = "Maximum number of nodes in a generated topology."
)
@Parameter(
  name = "branching_factor",
  defaultValue = "10",
  summary = "Number of children interior nodes expand to."
)
@Parameter(
  name = "topology_seed",
  defaultValue = "2",
  summary = "Base seed for topology generation; topology i uses topology_seed + i."
)
@Parameter(
  name = "urgent_path_length_fraction_min",
  defaultValue = "0.75",
  summary = "Minimum length of an urgent path as a fraction of the tree height."
)
@Parameter(
  name = "topology_count",
  defaultValue = "5",
  summary = "Number of distinct topologies to generate and run."
)
@Parameter(
  name = "temperature_tolerance",
  defaultValue = "1e-5",
  summary = "Acceptable floating-point deviation in temperature comparisons."
)
@Configuration(name = "test", settings = Array("topology_count = 1"))
@Configuration(name = "jmh", settings = Array("topology_count = 1"))
final class AkkaUct extends Benchmark {

  /**
   * The topology together with the shock temperature injected into the urgent leaves
   * by the urgent update, and the expected root temperatures before and after the shock.
   */
  private final case class Scenario(
    topology: Topology,
    shockTemperature: Double,
    expectedNominalTemperature: Double,
    expectedShockedTemperature: Double
  )

  /**
   * The result of a computation performed on one topology: the root temperature of the
   * reduction during which the urgent leaves are updated.
   */
  private final case class ScenarioResult(rootTemperature: Double)

  // Priority mailbox (prioritizing urgent nodes)
  private val systemFactory = new AkkaSystemFactory(
    "akka.dispatch.UnboundedControlAwareMailbox"
  )

  private var actorSystem: ActorSystem = _

  private var config: UctConfig = _
  private var scenarios: Array[Scenario] = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    config = UctConfig.fromContext(c)

    val topologyGenerator = new UctGenerator(config.nodeCountMax, config.branchingFactor)
    val urgentPathSelector = new UctUrgentPathSelector(
      config.urgentPathCount,
      config.urgentPathLengthFractionMin
    )

    // Pre-compute one scenario per topology. The urgent leaves are used only here.
    scenarios = Array.tabulate(config.topologyCount) { i =>
      val topology = topologyGenerator.build(new Random(config.topologySeed + i))

      val (annotatedInteriorNodes, urgentLeafIds) = urgentPathSelector.selectUrgentPaths(
        topology.interiorNodes,
        topology.branchingFactor,
        topology.height
      )

      val shockTemperature = AkkaUct.computeShockTemperature(
        topology,
        urgentLeafIds,
        config.rootShockMargin
      )

      val expectedNominalTemperature = AkkaUct.nominalRootTemperature(topology)
      val expectedShockedTemperature =
        AkkaUct.shockedRootTemperature(topology, urgentLeafIds.toSet, shockTemperature)

      println(
        s"[topology $i] nodes=${topology.nodeCount} levels=${topology.height + 1}" +
          s" urgentLeafIds=$urgentLeafIds"
      )

      Scenario(
        topology.copy(interiorNodes = annotatedInteriorNodes),
        shockTemperature,
        expectedNominalTemperature,
        expectedShockedTemperature
      )
    }
  }

  override def setUpBeforeEach(c: BenchmarkContext): Unit = {
    actorSystem = systemFactory.newActorSystem("UCT")
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val results = scenarios.map { scenario =>
      runScenario(actorSystem, scenario)
    }

    Validators.compound(() =>
      validateRootTemperatures(scenarios, results, config.temperatureTolerance)
    )
  }

  /** Applies the check to the scenario and the result of each topology. */
  private def forEachTopology(scenarios: Array[Scenario], results: Array[ScenarioResult])(
    check: (Int, Scenario, ScenarioResult) => Unit
  ): Unit =
    scenarios.zip(results).zipWithIndex.foreach {
      case ((scenario, result), topologyIndex) => check(topologyIndex, scenario, result)
    }

  /**
   * Checks that the root temperature of the reduction with the urgent update lies between
   * the nominal and the shocked temperature. The tolerance absorbs floating-point
   * differences, which arise because nodes add up the readings of their children in the
   * order of arrival.
   */
  private def validateRootTemperatures(
    scenarios: Array[Scenario],
    results: Array[ScenarioResult],
    tolerance: Double
  ): Unit =
    forEachTopology(scenarios, results) { (topologyIndex, scenario, result) =>
      val lowerBound = scenario.expectedNominalTemperature - tolerance
      val upperBound = scenario.expectedShockedTemperature + tolerance

      val temperature = result.rootTemperature
      if (temperature <= lowerBound || temperature >= upperBound) {
        throw new ValidationException(
          s"temperature for topology $topologyIndex not in range" +
            s" ($lowerBound, $upperBound): $temperature"
        )
      }
    }

  /** Creates the UCT of the scenario, takes the reductions, and destroys the UCT. */
  private def runScenario(system: ActorSystem, scenario: Scenario): ScenarioResult = {
    val resultPromise = Promise[Double]()

    system.actorOf(
      Props(new UctRootActor(scenario.topology, scenario.shockTemperature, resultPromise))
    ) ! GenerateTreeMessage

    ScenarioResult(Await.result(resultPromise.future, Duration.Inf))
  }

  override def tearDownAfterEach(c: BenchmarkContext): Unit = {
    Await.result(actorSystem.terminate(), Duration.Inf)
    actorSystem = null
  }
}

private[actors] object AkkaUct {

  /**
   * Computes the minimum shock temperature guaranteeing that the root temperature
   * shifts from its nominal value by at least [[rootMargin]] even if only one urgent
   * leaf is updated before it reports its temperature.
   *
   * A leaf at depth `d` contributes
   * `(shockTemperature - leafInitialTemperature) / branchingFactor^d` to the root delta
   * (each averaging step towards the root divides by the branching factor). The worst
   * case is the deepest urgent leaf (smallest contribution) with the highest initial
   * temperature:
   *
   *   shockTemperature >= LeafNode.InitialTemperatureMax
   *     + rootMargin * branchingFactor^urgentLeafDepthMax
   */
  def computeShockTemperature(
    topology: Topology,
    urgentLeafIds: List[NodeId],
    rootMargin: Double
  ): Double = {
    val urgentLeafDepthMax = urgentLeafIds.map(topology.leafDepths).max
    val deepestLeafDilution = math.pow(topology.branchingFactor, urgentLeafDepthMax)
    LeafNode.InitialTemperatureMax + rootMargin * deepestLeafDilution
  }

  /** Root temperature with all leaves at their initial temperature. */
  def nominalRootTemperature(topology: Topology): Double =
    rootTemperature(topology, LeafNode.initialTemperatureOf)

  /** Root temperature with every urgent leaf at the shock temperature. */
  def shockedRootTemperature(
    topology: Topology,
    urgentLeafIds: Set[NodeId],
    shockTemperature: Double
  ): Double =
    rootTemperature(
      topology,
      leafId =>
        if (urgentLeafIds.contains(leafId)) shockTemperature
        else LeafNode.initialTemperatureOf(leafId)
    )

  /**
   * Computes the root temperature bottom-up, as the actors do: every interior node
   * averages the temperatures of its children.
   */
  private def rootTemperature(topology: Topology, leafTemperatureOf: NodeId => Double): Double =
    topology.fold(leafTemperatureOf) { childTemperatures =>
      childTemperatures.sum / childTemperatures.length
    }
}
