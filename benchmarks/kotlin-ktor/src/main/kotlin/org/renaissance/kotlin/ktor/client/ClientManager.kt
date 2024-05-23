package org.renaissance.kotlin.ktor.client

import io.ktor.client.*
import io.ktor.util.*
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.CoroutineStart
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import kotlin.random.Random

/**
 * A **probabilistic** client manager, which sets up the appropriate number of clients, performing a specified number and kind of tasks
 */
class ClientManager(
  private val port: Int,
  numberOfClients: Int,
  private val numberOfRequestsPerClient: Int,
  private val fractionOfClientsSendingGroupMessages: Double,
  private val fractionOfClientsSendingPrivateMessages: Double,
  randomSeed: Int,
  private val coroutineScope: CoroutineScope
) {
  private val random = Random(randomSeed)
  private val userIds: Set<String> = (0..<numberOfClients).map { generateNonce() }.toSet()
  private val predefinedHttpClients: MutableList<HttpClient> = mutableListOf()
  private val clients: MutableList<Client> = mutableListOf()

  fun setupClients(availableChatIds: List<String>) {
    clients.clear()
    predefinedHttpClients.forEach { it.close() }
    predefinedHttpClients.clear()
    predefinedHttpClients.addAll(userIds.indices.map { createDefaultClient() })

    val clientBuilders = userIds.zip(predefinedHttpClients).map { (userId, httpClient) ->
      Client.Builder(port, userId, numberOfRequestsPerClient, httpClient)
    }.toMutableList()

    clientBuilders.take((userIds.size * fractionOfClientsSendingGroupMessages).toInt()).forEach { builder ->
      builder.addTaskToRun(JoinGroupAndSendMessageClientTask(availableChatIds.random(random), random))
    }
    clientBuilders.shuffle(random)

    clientBuilders.take((userIds.size * fractionOfClientsSendingPrivateMessages).toInt()).forEach { builder ->
      builder.addTaskToRun(DirectMessageClientTask(userIds.shuffled(random).first { it != builder.userId }, random))
    }
    clientBuilders.shuffle(random)

    clients.addAll(clientBuilders.map { it.build() })
  }

  suspend fun runClients(): Int {
    return clients.map { coroutineScope.async(start = CoroutineStart.LAZY) { it.run() } }
      .map { it.also { it.start() } }
      .awaitAll()
      .sum()
  }
}