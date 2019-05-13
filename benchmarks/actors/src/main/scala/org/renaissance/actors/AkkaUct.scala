package org.renaissance.actors

import edu.rice.habanero.actors.AkkaActorState
import edu.rice.habanero.benchmarks.uct.UctAkkaActorBenchmark
import org.renaissance.Benchmark._
import org.renaissance.{Config, License, RenaissanceBenchmark}

class AkkaUct extends RenaissanceBenchmark {
  override def description(): String =
    "Runs the Unbalanced Cobwebbed Tree actor workload in Akka."

  override def licenses(): Array[License] = License.create(License.MIT)

  override def defaultRepetitions = 24

  private var bench: UctAkkaActorBenchmark.UctAkkaActorBenchmark = null

  private var numIterations: Int = 10

  override def setUpBeforeAll(c: Config): Unit = {
    bench = new UctAkkaActorBenchmark.UctAkkaActorBenchmark
    bench.initialize(new Array[String](0))
    AkkaActorState.initialize()

    if (c.functionalTest) {
      numIterations = 2
    }
  }

  override def tearDownAfterAll(c: Config): Unit = {
    if (bench != null) {
      bench.cleanupIteration(false, 0)
    }
  }

  protected override def runIteration(config: Config): Unit = {
    for (i <- 0 until numIterations) {
      bench.runIteration()
    }
  }
}
