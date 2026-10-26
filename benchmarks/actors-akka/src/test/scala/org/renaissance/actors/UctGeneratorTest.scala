package org.renaissance.actors

import org.renaissance.actors.TestTopologies.generate
import org.renaissance.actors.TestTopologies.smallTopologyParameters
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.prop.TableDrivenPropertyChecks

import scala.collection.mutable

final class UctGeneratorTest extends AnyFunSuite with TableDrivenPropertyChecks {

  private def nodeIdsOf(topology: Topology): Set[NodeId] =
    topology.interiorNodes.keySet ++ topology.leafDepths.keySet

  test("topologies generated from the same seed are equal") {
    assert(generate(10000, 10, 42) == generate(10000, 10, 42))
  }

  test("topologies generated from different seeds differ") {
    assert(generate(10000, 10, 42) != generate(10000, 10, 43))
  }

  test("generated topologies stay within the node budget") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)

      assert(topology.nodeCount <= nodeCountMax)
    }
  }

  test("generated topologies number their nodes contiguously from the root") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)
      val interiorIds = topology.interiorNodes.keySet
      val leafIds = topology.leafDepths.keySet

      assert(interiorIds.intersect(leafIds).isEmpty)
      assert(nodeIdsOf(topology) == (0 until topology.nodeCount).map(NodeId(_)).toSet)
      assert(interiorIds.contains(NodeId.Root))
    }
  }

  test("every node except the root is a child of exactly one interior node") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)
      val childIds = topology.interiorNodes.values.toSeq.flatMap { expansion =>
        expansion.childIds(branchingFactor)
      }

      assert(childIds.size == topology.nodeCount - 1)
      assert(childIds.toSet == nodeIdsOf(topology) - NodeId.Root)
    }
  }

  test("generated topologies number their nodes in breadth-first order") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)
      val visitedIds = mutable.ArrayBuffer[NodeId]()
      val queue = mutable.Queue(NodeId.Root)
      while (queue.nonEmpty) {
        val nodeId = queue.dequeue()
        visitedIds += nodeId
        topology.interiorNodes.get(nodeId).foreach { expansion =>
          queue.enqueueAll(expansion.childIds(branchingFactor))
        }
      }

      assert(visitedIds == (0 until topology.nodeCount).map(NodeId(_)))
    }
  }

  test("leaf depths are the distances of the leaves from the root") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)

      def leafDepthsBelow(nodeId: NodeId, depth: Int): Map[NodeId, Int] =
        topology.interiorNodes.get(nodeId) match {
          case None => Map(nodeId -> depth)
          case Some(expansion) =>
            expansion
              .childIds(branchingFactor)
              .flatMap(childId => leafDepthsBelow(childId, depth + 1))
              .toMap
        }

      assert(leafDepthsBelow(NodeId.Root, 0) == topology.leafDepths)
    }
  }

  test("a topology generated from a fixed seed keeps its recorded size and leaf depths") {
    //
    // The structural tests accept any sequence of coin flips. Recording the shape of one
    // large topology detects a change in how the generator flips its coins, such as a
    // different expression or a different order of the flips.
    //
    val topology = generate(200000, 10, 2)
    val leafCountsByDepth = topology.leafDepths.values
      .groupBy(identity)
      .view
      .mapValues(_.size)
      .toSeq
      .sorted

    assert(topology.nodeCount == 199991)
    assert(
      leafCountsByDepth ==
        Seq(1 -> 4, 2 -> 28, 3 -> 164, 4 -> 800, 5 -> 3784, 6 -> 22932, 7 -> 152280)
    )
  }

}
