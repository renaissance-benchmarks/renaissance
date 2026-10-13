package org.renaissance.actors

import akka.actor.ActorSystem
import akka.actor.Props

import java.util.Random

import org.renaissance.Benchmark
import org.renaissance.Benchmark.*
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.ValidationException
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
@Parameter(name = "topology_count", defaultValue = "5")
@Configuration(name = "test", settings = Array("topology_count = 1"))
@Configuration(name = "jmh", settings = Array("topology_count = 1"))
final class AkkaUct extends Benchmark {
  import UctConfig.*

  // Priority mailbox (prioritizing urgent nodes)
  private val systemFactory = new AkkaSystemFactory(
    "akka.dispatch.UnboundedControlAwareMailbox"
  )

  private var actorSystem: ActorSystem = _
  private var topologyCount: Int = _
  private var topologies: Array[Topology] = _
  private var urgentLeaves: Array[List[NodeId]] = _
  private var shockTemperatures: Array[Double] = _
  private var expectedShockedTemperatures: Array[Double] = _
  private var expectedNominalTemperatures: Array[Double] = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    topologyCount = c.parameter("topology_count").toPositiveInteger

    // Pre-compute one topology per iteration.
    // Urgent leaves are kept separately for validation — never passed to actors.
    topologies = new Array[Topology](topologyCount)
    urgentLeaves = new Array[List[NodeId]](topologyCount)
    shockTemperatures = new Array[Double](topologyCount)
    expectedShockedTemperatures = new Array[Double](topologyCount)
    expectedNominalTemperatures = new Array[Double](topologyCount)

    val topologyGenerator = new UctGenerator(NodeCount, BranchingFactor)
    val urgentPathSelector = new UctUrgentPathSelector(
      UrgentPathCount,
      UrgentLeafDepthFractionMin
    )

    for (i <- 0 until topologyCount) {
      val topology = topologyGenerator.build(new Random(TopologySeed + i))

      val (annotatedInteriorNodes, urgentLeafIds) = urgentPathSelector.selectUrgentPaths(
        topology.interiorNodes,
        BranchingFactor,
        topology.height
      )

      topologies(i) = topology.copy(interiorNodes = annotatedInteriorNodes)
      urgentLeaves(i) = urgentLeafIds

      if (urgentLeafIds.nonEmpty) {
        val shockTemperature = AkkaUct.computeShockTemperature(
          topology,
          urgentLeafIds,
          RootShockMargin
        )
        shockTemperatures(i) = shockTemperature

        expectedNominalTemperatures(i) = AkkaUct.nominalRootTemperature(topology)
        expectedShockedTemperatures(i) =
          AkkaUct.shockedRootTemperature(topology, urgentLeafIds.toSet, shockTemperature)

        println(
          s"[topology $i] nodes=${topology.nodeCount} levels=${topology.height + 1}" +
            s" urgentLeafIds=$urgentLeafIds"
        )
      }
    }
  }

  override def setUpBeforeEach(c: BenchmarkContext): Unit = {
    actorSystem = systemFactory.newActorSystem("UCT")
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    val actualTemperatures = new Array[Double](topologyCount)

    for (i <- 0 until topologyCount) {
      actualTemperatures(i) = computeTopologyTemperature(topologies(i), shockTemperatures(i))
    }

    () => {
      for (i <- 0 until topologyCount) {
        val actual = actualTemperatures(i)
        val lowerBound = expectedNominalTemperatures(i) - TemperatureTolerance
        val upperBound = expectedShockedTemperatures(i) + TemperatureTolerance

        val temperatureWithinRange = lowerBound < actual && actual < upperBound
        if (!temperatureWithinRange) {
          throw new ValidationException(
            s"temperature for topology $i not in range ($lowerBound, $upperBound): $actual"
          )
        }
      }
    }
  }

  private def computeTopologyTemperature(
    topology: Topology,
    shockTemperature: Double
  ): Double = {
    val resultPromise = Promise[Double]()

    actorSystem.actorOf(
      Props(new UctRootActor(topology, shockTemperature, resultPromise))
    ) ! GenerateTreeMessage

    Await.result(resultPromise.future, Duration.Inf)
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
