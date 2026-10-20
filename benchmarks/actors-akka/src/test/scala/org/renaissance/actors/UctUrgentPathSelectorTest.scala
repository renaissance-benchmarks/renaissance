package org.renaissance.actors

import org.renaissance.actors.TestTopologies.generate
import org.renaissance.actors.TestTopologies.smallTopologyParameters
import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.prop.TableDrivenPropertyChecks

final class UctUrgentPathSelectorTest extends AnyFunSuite with TableDrivenPropertyChecks {

  private val pathLengthFractions = Table("pathLengthFractionMin", 0.0, 0.5, 0.9, 1.0)

  private val selectionParameters = Table(
    ("pathCount", "pathLengthFractionMin"),
    (for {
      pathCount <- Seq(1, 3, 8, 50)
      pathLengthFractionMin <- Seq(0.0, 0.5, 0.9, 1.0)
    } yield (pathCount, pathLengthFractionMin))*
  )

  /** The root-first paths to the leaves at least `pathLengthMin` deep, by leaf. */
  private def pathsToLeaves(
    topology: Topology,
    pathLengthMin: Int
  ): Map[NodeId, List[NodeId]] = {
    def pathsBelow(path: List[NodeId]): Seq[List[NodeId]] =
      topology.interiorNodes.get(path.last) match {
        case None => Seq(path)
        case Some(expansion) =>
          expansion
            .childIds(topology.branchingFactor)
            .flatMap(childId => pathsBelow(path :+ childId))
      }

    pathsBelow(List(NodeId.Root))
      .filter(path => path.length - 1 >= pathLengthMin)
      .map(path => path.last -> path)
      .toMap
  }

  /**
   * Selects the urgent leaves by comparing every remaining candidate path with every
   * selected path in each round. The overlap of a candidate is the depth of the deepest
   * node that it shares with a selected path, which is one less than the length of their
   * common prefix.
   */
  private def referenceUrgentLeaves(
    topology: Topology,
    pathCount: Int,
    pathLengthFractionMin: Double
  ): List[NodeId] = {
    val pathLengthMin =
      UctUrgentPathSelector.pathLengthMinOf(topology.height, pathLengthFractionMin)
    val candidatePaths = pathsToLeaves(topology, pathLengthMin).values.toList

    def commonPrefixLength(a: List[NodeId], b: List[NodeId]): Int =
      a.zip(b).takeWhile((x, y) => x == y).length

    def overlap(path: List[NodeId], selectedPaths: List[List[NodeId]]): Int =
      selectedPaths
        .map(selected => commonPrefixLength(path, selected))
        .maxOption
        .getOrElse(0) - 1

    val selectCount = math.min(pathCount, candidatePaths.length)
    Iterator
      .iterate((List.empty[List[NodeId]], candidatePaths)) { (selectedPaths, remainingPaths) =>
        val next = remainingPaths.minBy { path =>
          (overlap(path, selectedPaths), -path.length, path.last)
        }
        (selectedPaths :+ next, remainingPaths.filterNot(_ == next))
      }
      .drop(selectCount)
      .next()
      ._1
      .map(path => path.last)
  }

  test("the selection matches a selection comparing every candidate in every round") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)

      forAll(selectionParameters) { (pathCount, pathLengthFractionMin) =>
        val selector = new UctUrgentPathSelector(pathCount, pathLengthFractionMin)

        assert(
          selector.selectUrgentLeaves(topology) ==
            referenceUrgentLeaves(topology, pathCount, pathLengthFractionMin)
        )
      }
    }
  }

  test("the first urgent leaf is the farthest one, with the smallest ID among equals") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)
      val (farthestLeafId, _) = topology.leafDepths.minBy((leafId, depth) => (-depth, leafId))

      val urgentLeafIds = new UctUrgentPathSelector(3, 0.5).selectUrgentLeaves(topology)
      assert(urgentLeafIds.head == farthestLeafId)
    }
  }

  test("urgent leaves are distinct and lie at least at the minimum path length") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)

      forAll(pathLengthFractions) { pathLengthFractionMin =>
        val pathLengthMin =
          UctUrgentPathSelector.pathLengthMinOf(topology.height, pathLengthFractionMin)
        val urgentLeafIds =
          new UctUrgentPathSelector(50, pathLengthFractionMin).selectUrgentLeaves(topology)

        assert(urgentLeafIds.distinct == urgentLeafIds)
        assert(urgentLeafIds.forall(leafId => topology.leafDepths(leafId) >= pathLengthMin))
      }
    }
  }

  test("all qualifying paths are selected when fewer qualify than requested") {
    forAll(smallTopologyParameters) { (nodeCountMax, branchingFactor, seed) =>
      val topology = generate(nodeCountMax, branchingFactor, seed)

      forAll(pathLengthFractions) { pathLengthFractionMin =>
        val pathLengthMin =
          UctUrgentPathSelector.pathLengthMinOf(topology.height, pathLengthFractionMin)
        val qualifyingLeafIds = pathsToLeaves(topology, pathLengthMin).keySet
        val urgentLeafIds = new UctUrgentPathSelector(topology.nodeCount, pathLengthFractionMin)
          .selectUrgentLeaves(topology)

        assert(urgentLeafIds.toSet == qualifyingLeafIds)
      }
    }
  }

  test("the minimum path length lies between 1 and the height") {
    forAll(Table("height", (1 to 20)*)) { height =>
      forAll(Table("pathLengthFractionMin", 0.0, 0.5, 0.9, 1.0, 1.5)) { pathLengthFractionMin =>
        val pathLengthMin = UctUrgentPathSelector.pathLengthMinOf(height, pathLengthFractionMin)

        assert(pathLengthMin >= 1 && pathLengthMin <= height)
      }
    }
  }

}
