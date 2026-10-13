package org.renaissance.actors

import akka.actor.ActorRef
import akka.actor.ActorSystem
import akka.actor.DeadLetter
import akka.actor.Props
import akka.actor.UnhandledMessage

import java.util.Random
import java.util.concurrent.TimeUnit

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
import scala.concurrent.duration.FiniteDuration

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
 * For each topology, the benchmark requests several measurements at once and then sends
 * an [[UrgentUpdateTemperatureMessage]] (a [[akka.dispatch.ControlMessage]]) down a set
 * of urgent root-to-leaf paths selected by [[UctUrgentPathSelector]], setting the urgent
 * leaves to a shock temperature. The priority mailbox delivers the update before any
 * measurement request still waiting in the same mailbox, so the later measurements
 * observe the updated temperatures. One more measurement, requested after the update,
 * observes all urgent leaves at the shock temperature.
 *
 * The expected root temperatures are computed analytically as the bottom-up average over
 * all leaves: nominal with every leaf at its initial temperature, shocked with every
 * urgent leaf at the per-topology shock temperature derived from urgent leaf depths (see
 * [[AkkaUct.computeShockTemperature]]). The root temperatures of the measurements
 * requested before the update must lie between the two, must not decrease from one
 * measurement to the next, and in at least one topology, they must show the urgent update.
 * The root temperature of the measurement requested after the update must be the shocked
 * one.
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
  defaultValue = "0.9",
  summary = "Minimum length of an urgent path as a fraction of the tree height."
)
@Parameter(
  name = "topology_count",
  defaultValue = "5",
  summary = "Number of distinct topologies to generate and run."
)
@Parameter(
  name = "measurement_count",
  defaultValue = "3",
  summary = "Temperature measurements requested at once per topology, before the urgent update."
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
   * The result of a computation performed on one topology: the root temperatures of the
   * measurements racing the urgent update (in the order of the requests), and the root
   * temperature of the measurement requested after the update.
   */
  private final case class ScenarioResult(
    racingRootTemperatures: IndexedSeq[Double],
    rootTemperatureAfterUpdate: Double
  )

  // Priority mailbox (prioritizing control messages over regular messages)
  private val systemFactory = new AkkaSystemFactory(
    "akka.dispatch.UnboundedControlAwareMailbox"
  )

  private var actorSystem: ActorSystem = _

  /**
   * Collects the benchmark messages that end up as dead letters or are not handled by
   * their recipient in the current [[actorSystem]].
   */
  private var collector: ActorRef = _

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

    collector = actorSystem.actorOf(Props(new UctCollectorActor))
    actorSystem.eventStream.subscribe(collector, classOf[DeadLetter])
    actorSystem.eventStream.subscribe(collector, classOf[UnhandledMessage])
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val results = scenarios.map { scenario =>
      runScenario(actorSystem, scenario, config)
    }

    val unexpectedMessages = takeCollectedMessages(collector)

    Validators.compound(
      () => validateNoUnexpectedMessages(unexpectedMessages),
      () => validateRacingTemperatureRanges(scenarios, results, config.temperatureTolerance),
      () => validateRacingTemperatureOrder(scenarios, results, config.temperatureTolerance),
      () => validateUrgentUpdateShown(scenarios, results, config.temperatureTolerance),
      () => validateTemperaturesAfterUpdate(scenarios, results, config.temperatureTolerance)
    )
  }

  /** Checks that no benchmark message ended up as a dead letter or went unhandled. */
  private def validateNoUnexpectedMessages(messages: Seq[UctMessage]): Unit =
    if (messages.nonEmpty) {
      throw new ValidationException(
        s"${messages.size} unexpected messages, the first being ${messages.head}"
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
   * Checks that the root temperatures of the measurements racing the urgent update lie
   * between the nominal and the shocked temperature. The tolerance absorbs floating-point
   * differences, which arise because nodes add up the readings of their children in the
   * order of arrival.
   */
  private def validateRacingTemperatureRanges(
    scenarios: Array[Scenario],
    results: Array[ScenarioResult],
    tolerance: Double
  ): Unit =
    forEachTopology(scenarios, results) { (topologyIndex, scenario, result) =>
      val lowerBound = scenario.expectedNominalTemperature - tolerance
      val upperBound = scenario.expectedShockedTemperature + tolerance

      result.racingRootTemperatures.zipWithIndex.foreach { (temperature, measurementIndex) =>
        if (temperature < lowerBound || temperature > upperBound) {
          throw new ValidationException(
            s"temperature of measurement $measurementIndex for topology $topologyIndex" +
              s" not in range [$lowerBound, $upperBound]: $temperature"
          )
        }
      }
    }

  /**
   * Checks that the root temperatures of the measurements racing the urgent update do not
   * decrease from one measurement to the next.
   */
  private def validateRacingTemperatureOrder(
    scenarios: Array[Scenario],
    results: Array[ScenarioResult],
    tolerance: Double
  ): Unit =
    forEachTopology(scenarios, results) { (topologyIndex, _, result) =>
      val temperatures = result.racingRootTemperatures
      temperatures.zip(temperatures.tail).zipWithIndex.foreach {
        case ((earlier, later), earlierIndex) =>
          if (later < earlier - tolerance) {
            throw new ValidationException(
              s"temperature for topology $topologyIndex decreases from $earlier" +
                s" (measurement $earlierIndex) to $later (measurement ${earlierIndex + 1})"
            )
          }
      }
    }

  /**
   * Checks that some measurement racing the urgent update shows the update. The urgent
   * update overtakes the racing measurement requests only by chance, so in a single
   * topology, no racing measurement may show the update. Without a working priority
   * mailbox, however, no racing measurement can show it in any topology, so it is enough
   * that the update shows in one of them.
   */
  private def validateUrgentUpdateShown(
    scenarios: Array[Scenario],
    results: Array[ScenarioResult],
    tolerance: Double
  ): Unit = {
    val updateShown = scenarios.zip(results).exists { (scenario, result) =>
      val lowerBound = scenario.expectedNominalTemperature + tolerance
      result.racingRootTemperatures.exists(temperature => temperature > lowerBound)
    }

    if (!updateShown) {
      throw new ValidationException(
        "no measurement racing the urgent update shows the update in any topology"
      )
    }
  }

  /** Checks that the measurement after the urgent update shows the shocked temperature. */
  private def validateTemperaturesAfterUpdate(
    scenarios: Array[Scenario],
    results: Array[ScenarioResult],
    tolerance: Double
  ): Unit =
    forEachTopology(scenarios, results) { (topologyIndex, scenario, result) =>
      val expectedTemperature = scenario.expectedShockedTemperature
      val temperatureAfterUpdate = result.rootTemperatureAfterUpdate

      if (math.abs(temperatureAfterUpdate - expectedTemperature) > tolerance) {
        throw new ValidationException(
          s"temperature after the urgent update for topology $topologyIndex is" +
            s" $temperatureAfterUpdate instead of $expectedTemperature"
        )
      }
    }

  /**
   * Creates the UCT of the scenario, requests all racing measurements at once followed
   * by the urgent update and one more measurement, and destroys the UCT.
   */
  private def runScenario(
    system: ActorSystem,
    scenario: Scenario,
    config: UctConfig
  ): ScenarioResult = {
    val coordinator = system.actorOf(
      Props(new UctCoordinatorActor(scenario.topology))
    )

    val uctCreatedPromise = Promise[Unit]()
    coordinator ! LocalCreateUctMessage(uctCreatedPromise)
    Await.result(uctCreatedPromise.future, AkkaUct.PhaseTimeout)

    val racingPromises = IndexedSeq.fill(config.measurementCount)(Promise[Double]())
    racingPromises.foreach { promise =>
      coordinator ! LocalMeasureTemperatureMessage(promise)
    }
    coordinator ! LocalUrgentUpdateTemperatureMessage(scenario.shockTemperature)

    // Messages between two actors arrive in the order in which they were sent, and the
    // priority mailbox only moves the urgent update further ahead. The update therefore
    // reaches every urgent leaf before this request, so the measurement observes all urgent
    // leaves at the shock temperature.
    val afterUpdatePromise = Promise[Double]()
    coordinator ! LocalMeasureTemperatureMessage(afterUpdatePromise)

    val racingTemperatures = racingPromises.map { promise =>
      Await.result(promise.future, AkkaUct.PhaseTimeout)
    }
    val afterUpdateTemperature = Await.result(afterUpdatePromise.future, AkkaUct.PhaseTimeout)

    val uctDestroyedPromise = Promise[Unit]()
    coordinator ! LocalDestroyUctMessage(uctDestroyedPromise)
    Await.result(uctDestroyedPromise.future, AkkaUct.PhaseTimeout)

    ScenarioResult(racingTemperatures, afterUpdateTemperature)
  }

  /**
   * Takes the messages collected so far by the collector. Messages that reach the
   * collector later, such as during the shutdown of the actor system, are not checked.
   */
  private def takeCollectedMessages(collector: ActorRef): Seq[UctMessage] = {
    val resultPromise = Promise[Seq[UctMessage]]()
    collector ! LocalTakeCollectedMessagesMessage(resultPromise)
    Await.result(resultPromise.future, AkkaUct.PhaseTimeout)
  }

  override def tearDownAfterEach(c: BenchmarkContext): Unit = {
    Await.result(actorSystem.terminate(), AkkaUct.PhaseTimeout)
    actorSystem = null
  }
}

private[actors] object AkkaUct {

  /**
   * Maximum time to wait for a phase (tree creation, a measurement, tree destruction)
   * or for the actor system to terminate. A lost message makes the benchmark fail
   * instead of waiting forever. One minute is far longer than any phase takes in a
   * configuration that completes an iteration in reasonable time.
   */
  private val PhaseTimeout: FiniteDuration = Duration.create(1, TimeUnit.MINUTES)

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
