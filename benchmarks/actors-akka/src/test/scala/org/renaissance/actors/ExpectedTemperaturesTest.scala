package org.renaissance.actors

import org.renaissance.actors.TestTopologies.generate
import org.renaissance.actors.TestTopologies.smallTopologyParameters
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.prop.TableDrivenPropertyChecks

final class ExpectedTemperaturesTest extends AnyFunSuite with TableDrivenPropertyChecks {

  private val rootMargin = 1e-2
  private val urgentPathSelector = new UctUrgentPathSelector(8, 0.9)

  /** The urgent leaves of the topology and the shock temperature computed for them. */
  private def urgentLeavesAndShockTemperatureOf(topology: Topology): (List[NodeId], Double) = {
    val urgentLeafIds = urgentPathSelector.selectUrgentLeaves(topology)
    (urgentLeafIds, AkkaUct.computeShockTemperature(topology, urgentLeafIds, rootMargin))
  }

  test("initial leaf temperatures lie between zero and the maximum initial temperature") {
    (1 to 100000).map(NodeId(_)).foreach { leafId =>
      val temperature = LeafNode.initialTemperatureOf(leafId)
      assert(temperature > 0 && temperature < LeafNode.InitialTemperatureMax, leafId)
    }
  }

  test("the nominal root temperature is the depth-weighted sum of the leaf temperatures") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)
      val weightedSum = topology.leafDepths.toSeq.map { (leafId, depth) =>
        LeafNode.initialTemperatureOf(leafId) / math.pow(branchingFactor, depth)
      }.sum

      assert(math.abs(AkkaUct.nominalRootTemperature(topology) - weightedSum) < 1e-12)
    }
  }

  test("the shock temperature exceeds the initial temperature of every leaf") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)
      val (_, shockTemperature) = urgentLeavesAndShockTemperatureOf(topology)

      topology.leafDepths.keys.foreach { leafId =>
        assert(shockTemperature > LeafNode.initialTemperatureOf(leafId), leafId)
      }
    }
  }

  test("shocking only the deepest urgent leaf shifts the root temperature by the margin") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)
      val (urgentLeafIds, shockTemperature) = urgentLeavesAndShockTemperatureOf(topology)
      val deepestUrgentLeafId = urgentLeafIds.maxBy(topology.leafDepths)

      val shockedTemperature = AkkaUct.shockedRootTemperature(
        topology,
        Set(deepestUrgentLeafId),
        shockTemperature
      )
      val shift = shockedTemperature - AkkaUct.nominalRootTemperature(topology)

      // The averages along the path to the root can round the shift slightly below the margin.
      assert(shift >= rootMargin * (1 - 1e-9))
    }
  }

  test("the shocked root temperature exceeds the nominal root temperature") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)
      val (urgentLeafIds, shockTemperature) = urgentLeavesAndShockTemperatureOf(topology)

      val shockedTemperature =
        AkkaUct.shockedRootTemperature(topology, urgentLeafIds.toSet, shockTemperature)
      assert(shockedTemperature > AkkaUct.nominalRootTemperature(topology))
    }
  }

}
