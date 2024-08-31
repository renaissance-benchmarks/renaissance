package org.renaissance.http4k

import org.http4k.client.OkHttp
import org.renaissance.Benchmark
import org.renaissance.Benchmark.*
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License
import org.renaissance.http4k.workload.WorkloadClient
import org.renaissance.http4k.workload.WorkloadConfiguration
import org.renaissance.http4k.workload.WorkloadServer

@Name("http4k")
@Group("kotlin")
@Summary("Runs the http4k server and tests the throughput of the server by sending requests to the server.")
@SupportsJvm("21")
@Licenses(License.APACHE2)
@Repetitions(10)
@Parameter(
    name = "host",
    defaultValue = "localhost",
    summary = "Host of the server."
)
@Parameter(
    name = "port",
    defaultValue = "8000",
    summary = "Port of the server."
)
@Parameter(
    name = "read_workload_repeat_count",
    defaultValue = "100",
    summary = "Number of read requests to generate."
)
@Parameter(
    name = "write_workload_repeat_count",
    defaultValue = "100",
    summary = "Number of write requests to generate."
)
@Parameter(
    name = "ddos_workload_repeat_count",
    defaultValue = "100",
    summary = "Number of ddos requests to generate."
)
@Parameter(
    name = "mixed_workload_repeat_count",
    defaultValue = "100",
    summary = "Number of mixed requests to generate."
)
@Parameter(
    name = "workload_count",
    defaultValue = "100",
    summary = "Number of workloads to generate. Each workload consists of read, write, ddos and mixed requests."
)
@Parameter(
    name = "max_threads",
    defaultValue = "8",
    summary = "Maximum number of threads to use for the executor of the requests."
)
@Parameter(
    name = "workload_selector_seed",
    defaultValue = "0",
    summary = "Seed used to generate random workloads."
)
@Configuration(name = "jmh")
class Http4kBenchmark : Benchmark {
    private lateinit var server: WorkloadServer
    private lateinit var client: WorkloadClient

    override fun run(context: BenchmarkContext): BenchmarkResult {
        client.workload()
        return Validators.simple("Expected validation", 0, 0)
    }

    override fun setUpBeforeEach(context: BenchmarkContext) {
        val configuration = context.toWorkloadConfiguration()
        server = configuration.toWorkloadServer()
        client = configuration.toWorkloadClient()
        server.start()
    }

    override fun tearDownAfterEach(context: BenchmarkContext) {
        server.stop()
    }

    private fun BenchmarkContext.toWorkloadConfiguration(): WorkloadConfiguration = WorkloadConfiguration(
        host = parameter("host").value(),
        port = parameter("port").value().toInt(),
        readWorkloadRepeatCount = parameter("read_workload_repeat_count").value().toInt(),
        writeWorkloadRepeatCount = parameter("write_workload_repeat_count").value().toInt(),
        ddosWorkloadRepeatCount = parameter("ddos_workload_repeat_count").value().toInt(),
        mixedWorkloadRepeatCount = parameter("mixed_workload_repeat_count").value().toInt(),
        workloadCount = parameter("workload_count").value().toInt(),
        maxThreads = parameter("max_threads").value().toInt(),
        workloadSelectorSeed = parameter("workload_selector_seed").value().toLong()
    )

    private fun WorkloadConfiguration.toWorkloadClient(): WorkloadClient =
        WorkloadClient(OkHttp(), this)

    private fun WorkloadConfiguration.toWorkloadServer(): WorkloadServer =
        WorkloadServer(port)
}




