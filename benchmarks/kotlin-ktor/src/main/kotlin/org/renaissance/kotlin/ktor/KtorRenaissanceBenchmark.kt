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
  summary = "Clients which execute joinChatAndSendMessage"
)
@Parameter(
  name = "private_message_fraction",
  defaultValue = "0.5",
  summary = "How many public chats should be setup for user interactions"
)
@Parameter(
  name = "random_seed",
  defaultValue = "32",
  summary = "Random seed to use for client tasks setup."
)
class KtorRenaissanceBenchmark() : Benchmark {
  private var port: Int = 0
  private var clientCount: Int = 0
  private var numberOfRepetitions: Int = 0
  private var fractionOfClientsSendingPrivateMessages: Double = 0.0
  private var fractionOfClientsSendingGroupMessages: Double = 0.0
  private lateinit var clientPool: ExecutorCoroutineDispatcher
  private lateinit var server: ApplicationEngine
  private lateinit var application: ChatApplication
  private lateinit var clientManager: ClientManager

  @OptIn(DelicateCoroutinesApi::class)
  override fun setUpBeforeAll(context: BenchmarkContext?) {
    port = context!!.parameter("port").toPositiveInteger()
    clientCount = context.parameter("client_count").toPositiveInteger()
    numberOfRepetitions = context.parameter("iterations_count").toPositiveInteger()
    val numberOfChats = context.parameter("chat_count").toPositiveInteger()
    fractionOfClientsSendingGroupMessages = context.parameter("group_message_fraction").toDouble()
    fractionOfClientsSendingPrivateMessages =
      context.parameter("private_message_fraction").toDouble()
    val randomSeed = context.parameter("random_seed").toPositiveInteger()

    application = ChatApplication(numberOfChats)
    server = embeddedServer(io.ktor.server.cio.CIO, host = "localhost", port = port) {
      application.apply {
        main()
      }
    }
    server.start()

    clientPool = newFixedThreadPoolContext(min(clientCount, Runtime.getRuntime().availableProcessors()), "clientPool")
    clientManager = ClientManager(
      port,
      clientCount,
      numberOfRepetitions,
      fractionOfClientsSendingGroupMessages,
      fractionOfClientsSendingPrivateMessages,
      randomSeed,
      CoroutineScope(clientPool)
    )

    super.setUpBeforeAll(context)
  }

  override fun setUpBeforeEach(context: BenchmarkContext?) {
    application.setup()
    clientManager.setupClients(application.getAvailableChatIds())
  }

  override fun run(context: BenchmarkContext?): BenchmarkResult {
    val numberOfSuccessfulTasks = runBlocking {
      clientManager.runClients()
    }

    return Validators.simple(
      "Number of successful client tasks",
      (((clientCount * fractionOfClientsSendingGroupMessages) + (clientCount * fractionOfClientsSendingPrivateMessages)) * numberOfRepetitions).toLong(),
      numberOfSuccessfulTasks.toLong()
    )
  }

  override fun tearDownAfterAll(context: BenchmarkContext?) {
    server.stop()
    clientPool.close()
  }
}