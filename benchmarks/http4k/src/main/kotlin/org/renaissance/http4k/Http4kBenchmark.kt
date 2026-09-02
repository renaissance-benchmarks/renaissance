package org.renaissance.http4k

import kotlinx.coroutines.runBlocking
import org.http4k.client.OkHttp
import org.renaissance.Benchmark
import org.renaissance.Benchmark.Configuration
import org.renaissance.Benchmark.Group
import org.renaissance.Benchmark.Licenses
import org.renaissance.Benchmark.Name
import org.renaissance.Benchmark.Parameter
import org.renaissance.Benchmark.Repetitions
import org.renaissance.Benchmark.Summary
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License
import org.renaissance.http4k.workload.WorkloadClient
import org.renaissance.http4k.workload.WorkloadConfiguration
import org.renaissance.http4k.workload.WorkloadServer

@Name("http4k")
@Group("web")
@Group("http4k")
@Summary("Sends concurrent HTTP requests to an http4k server with an Undertow backend.")
@Licenses(License.APACHE2)
@Repetitions(20)
@Parameter(
    name = "host",
    defaultValue = "127.0.0.1",
    summary = "Host of the server."
)
@Parameter(
    name = "port",
    defaultValue = "0",
    summary = "Port of the server (0 for auto-allocation)."
)
@Parameter(
    name = "server_threads",
    defaultValue = "\$cpu.count",
    summary = "Number of Undertow worker threads."
)
@Parameter(
    name = "max_threads",
    defaultValue = "\$cpu.count",
    summary = "Maximum number of client coroutine threads."
)
@Parameter(
    name = "workload_count",
    defaultValue = "450",
    summary = "Number of workloads to generate."
)
@Parameter(
    name = "read_workload_repeat_count",
    defaultValue = "5",
    summary = "Number of read requests per workload."
)
@Parameter(
    name = "write_workload_repeat_count",
    defaultValue = "5",
    summary = "Number of write requests per workload."
)
@Parameter(
    name = "ddos_workload_repeat_count",
    defaultValue = "5",
    summary = "Number of ddos requests per workload."
)
@Parameter(
    name = "mixed_workload_repeat_count",
    defaultValue = "5",
    summary = "Number of mixed requests per workload."
)
@Parameter(
    name = "workload_selection_seed",
    defaultValue = "42",
    summary = "Seed used to generate random workloads."
)
@Configuration(
    name = "test",
    settings = [
        "server_threads = 2",
        "max_threads = 2",
        "workload_count = 100"
    ]
)
@Configuration(name = "jmh")
class Http4kBenchmark : Benchmark {
    private lateinit var server: WorkloadServer
    private lateinit var client: WorkloadClient
    private lateinit var configuration: WorkloadConfiguration

    override fun run(context: BenchmarkContext): BenchmarkResult = runBlocking {
        val workloadSummary = client.workload()
        Validators.simple("Workload count", configuration.workloadCount.toLong(), workloadSummary.workloadCount)
    }

    override fun setUpBeforeEach(context: BenchmarkContext) {
        configuration = context.toWorkloadConfiguration()
        server = WorkloadServer(configuration.port, configuration.serverThreads)
        server.start()

        // If port value is 0, server allocates a free port which has to be saved for client requests.
        configuration = configuration.copy(port = server.port())
        client = WorkloadClient(OkHttp(), configuration)
    }

    override fun tearDownAfterEach(context: BenchmarkContext) {
        server.stop()
    }

    private fun BenchmarkContext.toWorkloadConfiguration(): WorkloadConfiguration = WorkloadConfiguration(
        host = parameter("host").value(),
        port = parameter("port").value().toInt(),
        serverThreads = parameter("server_threads").value().toInt(),
        readWorkloadRepeatCount = parameter("read_workload_repeat_count").value().toInt(),
        writeWorkloadRepeatCount = parameter("write_workload_repeat_count").value().toInt(),
        ddosWorkloadRepeatCount = parameter("ddos_workload_repeat_count").value().toInt(),
        mixedWorkloadRepeatCount = parameter("mixed_workload_repeat_count").value().toInt(),
        workloadCount = parameter("workload_count").value().toInt(),
        maxThreads = parameter("max_threads").value().toInt(),
        workloadSelectionSeed = parameter("workload_selection_seed").value().toLong()
    )
}
