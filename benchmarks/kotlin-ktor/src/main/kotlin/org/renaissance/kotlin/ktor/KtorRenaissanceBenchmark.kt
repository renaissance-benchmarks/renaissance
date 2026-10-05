package org.renaissance.kotlin.ktor

import io.ktor.server.engine.*
import kotlinx.coroutines.*
import org.renaissance.Benchmark
import org.renaissance.Benchmark.*
import org.renaissance.BenchmarkContext
import org.renaissance.BenchmarkResult
import org.renaissance.BenchmarkResult.Validators
import org.renaissance.License
import org.renaissance.kotlin.ktor.client.ClientManager
import org.renaissance.kotlin.ktor.server.ChatApplication
import kotlin.math.min
import kotlin.random.Random

@Group("web")
@Name("kotlin-ktor")
@Summary("Simple Ktor chat application with multiple clients, performing various tasks.")
@Licenses(License.MIT)
@Parameter(
  name = "port",
  defaultValue = "9496",
  summary = "Port to run the server on."
)
@Parameter(
  name = "client_count",
  defaultValue = "\$cpu.count",
  summary = "Number of clients that are simultaneously sending the requests"
)
@Parameter(
  name = "iterations_count",
  defaultValue = "2000",
  summary = "Number of times clients should repeat their designated operations"
)
@Parameter(
  name = "chat_count",
  defaultValue = "10",
  summary = "How many public chats should be setup for user interactions." +
      "Reducing/increasing number of chats will increase/decrease runtime"
)
@Parameter(
  name = "group_message_fraction",
  defaultValue = "1.0",
  summary = "Fraction of clients sending messages to group chats."
)
@Parameter(
  name = "direct_message_fraction",
  defaultValue = "0.5",
  summary = "Fraction of clients sending direct messages."
)
@Parameter(
  name = "random_seed",
  defaultValue = "32",
  summary = "Seed for the base random generator from which other generators are derived."
)
@Configuration(
  name = "test",
  settings = [
    "iterations_count = 100",
  ]
)
@Configuration(name = "jmh")
class KtorRenaissanceBenchmark() : Benchmark {
  private lateinit var clientPool: ExecutorCoroutineDispatcher
  private lateinit var server: ApplicationEngine
  private lateinit var application: ChatApplication
  private lateinit var clientManager: ClientManager

  internal data class Parameters(
    val port: Int,
    val clientCount: Int,
    val clientRepetitionCount: Int,
    val chatCount: Int,
    val groupMessageFraction: Double,
    val directMessageFraction: Double,
    val randomSeed: Long
  ) {
    companion object {
      fun fromContext(context: BenchmarkContext) = Parameters(
        port = context.parameter("port").toPositiveInteger(),
        clientCount = context.parameter("client_count").toPositiveInteger(),
        clientRepetitionCount = context.parameter("iterations_count").toPositiveInteger(),
        chatCount = context.parameter("chat_count").toPositiveInteger(),
        groupMessageFraction = context.parameter("group_message_fraction").toDouble(),
        directMessageFraction = context.parameter("direct_message_fraction").toDouble(),
        randomSeed = context.parameter("random_seed").toPositiveInteger().toLong()
      )
    }
  }

  private fun startServer(application: ChatApplication, port: Int): ApplicationEngine {
    // Unlike the client side, we do not control the server side concurrency.
    // The CIOApplicationEngine hardcodes Dispatchers.IO and (as of Ktor 2.3.8)
    // ignores the inherited Configuration settings such as connectionGroupSize,
    // workerGroupSize, and callGroupSize. Using other application engines, such
    // as Netty, would defeat the purpose of using a Kotlin-native engine.
    val server = embeddedServer(io.ktor.server.cio.CIO, host = "127.0.0.1", port = port) {
      application.apply {
        main()
      }
    }

    // After start() returns, the server is ready to accept connections.
    server.start()
    return server
  }

  @OptIn(DelicateCoroutinesApi::class)
  private fun createClientPool(clientCount: Int): ExecutorCoroutineDispatcher =
    newFixedThreadPoolContext(min(clientCount, Runtime.getRuntime().availableProcessors()), "clientPool")

  private fun createClientManager(
    parameters: Parameters, clientPool: ExecutorCoroutineDispatcher, initialSeed: Long
  ) = ClientManager(parameters, CoroutineScope(clientPool), initialSeed)

  override fun setUpBeforeAll(context: BenchmarkContext) {
    val parameters = Parameters.fromContext(context)
    val baseRandom = Random(parameters.randomSeed)

    application = ChatApplication(parameters.chatCount, baseRandom.nextLong())
    server = startServer(application, parameters.port)

    clientPool = createClientPool(parameters.clientCount)
    clientManager = createClientManager(parameters, clientPool, baseRandom.nextLong())
  }

  override fun setUpBeforeEach(context: BenchmarkContext) {
    application.setup()
    clientManager.setupClients(application.getAvailableChatIds())
  }

  override fun run(context: BenchmarkContext): BenchmarkResult {
    val numberOfSuccessfulTasks = runBlocking {
      clientManager.runClients()
    }

    return Validators.simple(
      "Number of successful client tasks",
      clientManager.expectedSuccessfulTaskCount.toLong(),
      numberOfSuccessfulTasks.toLong()
    )
  }

  override fun tearDownAfterEach(context: BenchmarkContext) {
    clientManager.closeClients()
    application.teardown()
  }

  override fun tearDownAfterAll(context: BenchmarkContext) {
    clientPool.close()
    server.stop()
  }
}
