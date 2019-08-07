package org.renaissance.neo4j

import java.nio.file.Paths

import org.renaissance.Benchmark._
import org.renaissance.BenchmarkResult
import org.renaissance.License
import org.renaissance.neo4j.analytics.AnalyticsBenchmark
import org.renaissance.Benchmark
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult.Validators

@Name("neo4j-analytics")
@Group("neo4j")
@Summary("Executes Neo4J graph queries against a movie database.")
@Licenses(Array(License.GPL3))
@Repetitions(20)
// Work around @Repeatable annotations not working in this Scala version.
@Parameters(
  Array(
    new Parameter(name = "long_query_count", defaultValue = "2"),
    new Parameter(name = "short_query_count", defaultValue = "1"),
    new Parameter(name = "mutator_query_count", defaultValue = "1")
  )
)
@Configurations(Array(new Configuration(name = "test"), new Configuration(name = "jmh")))
final class Neo4jAnalytics extends Benchmark {

  // TODO: Unify handling of scratch directories throughout the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/13

  private val scratchPath = Paths.get("target", "modules", "neo4j", "neo4j-analytics.db")

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27

  private var longQueryCountParam: Int = _

  private var shortQueryCountParam: Int = _

  private var mutatorQueryCountParam: Int = _

  private var benchmark: AnalyticsBenchmark = _

  override def setUpBeforeAll(c: BenchmarkContext): Unit = {
    longQueryCountParam = c.intParameter("long_query_count")
    shortQueryCountParam = c.intParameter("short_query_count")
    mutatorQueryCountParam = c.intParameter("mutator_query_count")

    benchmark = new AnalyticsBenchmark(
      scratchPath.toFile,
      Option(longQueryCountParam),
      Option(shortQueryCountParam),
      Option(mutatorQueryCountParam)
    )

    benchmark.setupAll()
  }

  override def tearDownAfterAll(c: BenchmarkContext): Unit = {
    benchmark.tearAll()
  }

  override def run(config: BenchmarkContext): BenchmarkResult = {
    // TODO: Return something useful for validation
    benchmark.run()

    // TODO: add proper validation
    Validators.dummy(benchmark)
  }
}
