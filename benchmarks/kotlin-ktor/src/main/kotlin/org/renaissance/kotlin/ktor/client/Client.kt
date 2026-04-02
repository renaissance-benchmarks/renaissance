package org.renaissance.kotlin.ktor.client

import io.ktor.client.*
import io.ktor.client.engine.cio.*
import io.ktor.client.plugins.websocket.*
import io.ktor.http.*
import io.ktor.serialization.kotlinx.*
import org.renaissance.kotlin.ktor.common.serializationFormat


/**
 * Client is an abstraction for the list of tasks to perform **sequentially**.
 *
 * For example:
 * 1. Send a message to some User
 * 2. Send picture to some chat
 * 3. Join another chat
 * 4. Leave the chat
 */
internal class Client private constructor(
  private val httpClient: HttpClient,
  private val port: Int,
  private val userId: String,
  private val operationsRepetitions: Int,
  private val tasksToRun: List<ClientTask>,
) {
  /**
   * Runs the client by establishing a WebSocket connection and performing the specified tasks.
   *
   * @return The number of successful tasks. Should be equal to `operationsRepetitions * tasksToRun.length`
   */
  suspend fun run(): Int {
    var successfulTasks = 0
    httpClient.webSocket(method = HttpMethod.Get, host = "127.0.0.1", port = port, path = "/ws/${userId}") {
      tasksToRun.forEach { it.setup(this) }

      for (i in 0..<operationsRepetitions) {
        tasksToRun.forEach {
          try {
            it.run(this)
            successfulTasks++
          } catch (_: Throwable) {
          }
        }
      }
    }
    return successfulTasks
  }

  class Builder(
    private val port: Int,
    val userId: String,
    private val operationsRepetitions: Int,
    private val httpClient: HttpClient = createDefaultClient()
  ) {
    private val tasksToRun: MutableList<ClientTask> = mutableListOf()

    fun addTaskToRun(task: ClientTask): Builder {
      tasksToRun.add(task)
      return this
    }

    fun build(): Client {
      return Client(httpClient, port, userId, operationsRepetitions, tasksToRun)
    }
  }
}

fun createDefaultClient(): HttpClient = HttpClient(CIO) {
  engine {

  }
  install(WebSockets) {
    contentConverter = KotlinxWebsocketSerializationConverter(serializationFormat)
  }
}