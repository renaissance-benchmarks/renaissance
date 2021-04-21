package org.renaissance.actors

import edu.rice.habanero.actors.AkkaActorState
import edu.rice.habanero.benchmarks.uct.UctAkkaActorBenchmark
import org.renaissance.Benchmark
import org.renaissance.Benchmark._
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License

@Name("akka-uct")
@Group("actors")
@Summary("Runs the Unbalanced Cobwebbed Tree actor workload in Akka.")
@Licenses(Array(License.MIT))
@Repetitions(24)
@Parameter(name = "loop_count", defaultValue = "10")
@Configuration(name = "test", settings = Array("loop_count = 2"))
@Configuration(name = "jmh", settings = Array("loop_count = 1"))
final class AkkaUct extends Benchmark {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var loopCountParam: Int = _

  private var bench: UctAkkaActorBenchmark.UctAkkaActorBenchmark = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    loopCountParam = c.parameter("loop_count").toPositiveInteger

    bench = new UctAkkaActorBenchmark.UctAkkaActorBenchmark
    bench.initialize(new Array[String](0))
    AkkaActorState.initialize()
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    if (bench != null) {
      bench.cleanupIteration(lastIteration = false, 0)
    }
  }

  override def run(c: BenchmarkContext): BenchmarkResult = {
    for (_ <- 0 until loopCountParam) {
      bench.runIteration()
    }

    // TODO: add proper validation
    Validators.dummy()
  }
}
