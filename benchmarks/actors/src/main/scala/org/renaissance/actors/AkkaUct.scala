package org.renaissance.actors

import edu.rice.habanero.actors.AkkaActorState
import edu.rice.habanero.benchmarks.uct.UctAkkaActorBenchmark
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.License

@Name("akka-uct")
@Group("actors")
@Summary("Runs the Unbalanced Cobwebbed Tree actor workload in Akka.")
@Licenses(Array(License.MIT))
@Repetitions(24)
class AkkaUct extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var numIterations: Int = 10

  private var bench: UctAkkaActorBenchmark.UctAkkaActorBenchmark = null

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    bench = new UctAkkaActorBenchmark.UctAkkaActorBenchmark
    bench.initialize(new Array[String](0))
    AkkaActorState.initialize()

    if (c.functionalTest) {
      numIterations = 2
    }
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    if (bench != null) {
      bench.cleanupIteration(false, 0)
    }
  }

  override def runIteration(c: BenchmarkContext): BenchmarkResult = {
    for (i <- 0 until numIterations) {
      bench.runIteration()
    }

    // TODO: add proper validation
    BenchmarkResult.dummy()
  }
}
