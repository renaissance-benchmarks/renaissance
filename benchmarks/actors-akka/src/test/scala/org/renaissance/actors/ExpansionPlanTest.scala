package org.renaissance.actors

import org.renaissance.actors.TestTopologies.generate
import org.renaissance.actors.TestTopologies.smallTopologyParameters
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.prop.TableDrivenPropertyChecks

final class ExpansionPlanTest extends AnyFunSuite with TableDrivenPropertyChecks {

  test("a tree built by following the plan has the leaves and the checksum of the topology") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)
      val plan = ExpansionPlan.of(topology)

      //
      // Each node combines its own checksum with those of its children, as the node
      // actors do when the subtree below them is complete.
      //
      def buildBelow(nodeId: NodeId, depth: Int): (Map[NodeId, Int], TreeChecksum) =
        plan.expansionOf(nodeId) match {
          case None => (Map(nodeId -> depth), TreeChecksum.of(nodeId))
          case Some(expansion) =>
            val children = expansion.childIds(plan.childCount).map(buildBelow(_, depth + 1))
            val leafDepths = children.flatMap((childLeafDepths, _) => childLeafDepths).toMap
            val checksum = children.foldLeft(TreeChecksum.of(nodeId)) {
              case (checksum, (_, childChecksum)) => checksum.combinedWith(childChecksum)
            }
            (leafDepths, checksum)
        }

      val (leafDepths, checksum) = buildBelow(NodeId.Root, 0)
      assert(leafDepths == topology.leafDepths)
      assert(checksum == AkkaUct.treeChecksum(topology))
    }
  }

}
