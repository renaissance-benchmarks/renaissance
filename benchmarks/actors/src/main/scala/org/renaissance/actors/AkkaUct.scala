package org.renaissance.actors

import edu.rice.habanero.actors.AkkaActorState
import edu.rice.habanero.benchmarks.uct.UctAkkaActorBenchmark
import org.renaissance.Config
import org.renaissance.License
import org.renaissance.RenaissanceBenchmark
import org.renaissance.Benchmark._

@Name("akka-uct")
@Group("actors")
@Summary("Runs the Unbalanced Cobwebbed Tree actor workload in Akka.")
@Licenses(Array(License.MIT))
@Repetitions(24)
class AkkaUct extends RenaissanceBenchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var numIterations: Int = 10

  private var bench: UctAkkaActorBenchmark.UctAkkaActorBenchmark = null

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
