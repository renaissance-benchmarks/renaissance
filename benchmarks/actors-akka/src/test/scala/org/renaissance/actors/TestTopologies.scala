package org.renaissance.actors

import org.scalatest.prop.TableDrivenPropertyChecks.Table
import org.scalatest.prop.TableFor3

import java.util.Random

/** Generation of topologies for the tests. */
object TestTopologies {

  def generate(nodeCountMax: Int, branchingFactor: Int, seed: Long): Topology =
    new UctGenerator(nodeCountMax, branchingFactor).build(new Random(seed))

  /** Parameters of small topologies: up to 500 nodes, 3 to 10 children, 3 seeds each. */
  val smallTopologyParameters: TableFor3[Int, Int, Long] = Table(
    ("nodeCountMax", "branchingFactor", "seed"),
    (for {
      nodeCountMax <- Seq(50, 200, 500)
      branchingFactor <- Seq(3, 5, 10)
      seed <- Seq(3L, 517L, 90173L)
    } yield (nodeCountMax, branchingFactor, seed))*
  )

}
