package org.renaissance.http4k

import org.renaissance.Benchmark
import org.renaissance.Benchmark.*
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.License

@Name("http4k")
@Group("kotlin")
@Summary("Runs the http4k server and tests the throughput of the server by sending requests to the server.")
@Licenses(License.APACHE2)
@Repetitions(10)
@Parameter(
    name = "request_count",
    defaultValue = "10000",
    summary = "Number of requests to generate."
)
@Configuration(name = "jmh")
class Http4kBenchmark : Benchmark {
    override fun run(context: BenchmarkContext): BenchmarkResult {
        TODO("Not yet implemented")
    }
}