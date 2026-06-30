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

import scala.collection.mutable
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
 * UCT, the interior nodes average their children's readings while the leaves report
 * fixed values seeded by node ID.
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

    val urgentPathSelector = new UctUrgentPathSelector(
      UrgentPathCount,
      UrgentLeafDepthFractionMin
    )

    for (i <- 0 until topologyCount) {
      val topology = new UctGenerator(
        nodeCountMax = NodeCount,
        branchingFactor = BranchingFactor,
        rng = new Random(TopologySeed + i)
      ).build()

      val (annotatedInteriorNodes, urgentLeafIds) = urgentPathSelector.selectUrgentPaths(
        topology.interiorNodes,
        BranchingFactor,
        topology.maxDepth
      )

      topologies(i) = topology.copy(interiorNodes = annotatedInteriorNodes)
      urgentLeaves(i) = urgentLeafIds

      if (urgentLeafIds.nonEmpty) {
        val urgentLeavesSet = urgentLeafIds.toSet

        val shockTemperature = AkkaUct.computeShockTemperature(topologies(i), RootShockMargin)
        shockTemperatures(i) = shockTemperature

        val (shocked, nominal) = AkkaUct.analyticalRootTemperature(
          topologies(i),
          urgentLeavesSet,
          shockTemperature,
          LeafTemperatureSeed
        )

        expectedShockedTemperatures(i) = shocked
        expectedNominalTemperatures(i) = nominal

        println(
          s"[topology $i] nodes=${topologies(i).nodeCount} height=${topologies(i).maxDepth + 1}" +
            s" urgentLeafIds=${urgentLeaves(i)}"
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

object AkkaUct {

  /**
   * Computes the minimum shock temperature guaranteeing that the root temperature
   * shifts from its nominal value by at least [[rootMargin]] even if only one urgent
   * leaf is updated.
   *
   * A leaf at depth d contributes (shockTemperature - leafInitialTemperature) / branchingFactor^d
   * to the root delta (each tree level divides by the branching factor). The worst
   * case is the deepest urgent leaf (smallest contribution). Using 0.9 as the upper
   * bound of the initial temperature range [0.1, 0.9):
   *
   *   shockTemperature >= 0.9 + rootMargin * branchingFactor^maxUrgentDepth
   */
  def computeShockTemperature(topology: Topology, rootMargin: Double): Double = {
    val bf = UctConfig.BranchingFactor

    val depthOf = mutable.Map[NodeId, Int](0 -> 0)
    val queue = mutable.Queue[NodeId](0)
    while (queue.nonEmpty) {
      val nodeId = queue.dequeue()
      topology.interiorNodes.get(nodeId).foreach { node =>
        for (slot <- 0 until bf) {
          val childId = node.firstChildId + slot
          depthOf(childId) = depthOf(nodeId) + 1
          queue.enqueue(childId)
        }
      }
    }

    val maxUrgentLeafDepth = topology.interiorNodes.values.flatMap { node =>
      node.urgentChildSlots
        .map(slot => node.firstChildId + slot)
        .filter(childId => !topology.interiorNodes.contains(childId))
        .map(depthOf)
    }.max

    0.9 + rootMargin * math.pow(bf, maxUrgentLeafDepth)
  }

  /**
   * Compute the expected root temperatures bottom-up:
   *   _1 = shocked: every urgent leaf at shockTemperature
   *   _2 = nominal: all leaves at their normal deterministic initial temperature
   */
  def analyticalRootTemperature(
    topology: Topology,
    urgentLeaves: Set[NodeId],
    shockTemperature: Double,
    leafSeed: Long
  ): (Double, Double) = {
    val branchingFactor = UctConfig.BranchingFactor

    def recurseShocked(id: NodeId): Double =
      topology.interiorNodes.get(id) match {
        case None =>
          if (urgentLeaves.contains(id)) shockTemperature
          else leafInitialTemperature(id, leafSeed)
        case Some(node) =>
          var sum = 0.0
          var i = 0
          while (i < branchingFactor) {
            sum += recurseShocked(node.firstChildId + i)
            i += 1
          }
          sum / branchingFactor
      }

    def recurseNominal(id: NodeId): Double =
      topology.interiorNodes.get(id) match {
        case None => leafInitialTemperature(id, leafSeed)
        case Some(node) =>
          var sum = 0.0
          var i = 0
          while (i < branchingFactor) {
            sum += recurseNominal(node.firstChildId + i)
            i += 1
          }
          sum / branchingFactor
      }

    (recurseShocked(0), recurseNominal(0))
  }

  /**
   * Deterministic leaf temperature in [0.1, 0.9].
   * Uses a seeded per-node Random so that every leaf gets a distinct value that
   * is reproducible across actor runs and analytical computations.
   */
  def leafInitialTemperature(nodeId: NodeId, leafSeed: Long): Double = {
    val mixed = leafSeed ^ (nodeId.toLong * 0x9e3779b97f4a7c15L)
    val rng = new java.util.Random(mixed)
    rng.nextDouble() * 0.8 + 0.1
  }
}
