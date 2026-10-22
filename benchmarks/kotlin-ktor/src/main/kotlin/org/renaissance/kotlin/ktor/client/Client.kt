package org.renaissance.kotlin.ktor.client

import io.ktor.client.*
import io.ktor.client.engine.cio.*
import io.ktor.client.plugins.websocket.*
import io.ktor.http.*
import io.ktor.serialization.kotlinx.*
import org.renaissance.kotlin.ktor.common.User
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
  private val user: User,
  private val operationsRepetitions: Int,
  private val prologueTasks: List<ClientTask>,
  private val tasksToRun: List<ClientTask>,
) {
  /**
   * Runs the client by establishing a WebSocket connection and performing the specified tasks.
   *
   * The [prologueTasks] are intended for actions related to the client's
   * session (e.g., establishing a display name) and are run exactly once
   * before running the [tasksToRun] repeatedly.
   *
   * This is a localhost-only scenario, so every task is expected to execute
   * without throwing an exception. A task may return `false` if the response
   * from the server is not what the task expected. Task throwing an exception
   * means something is totally broken.
   *
   * @return The number of tasks that completed with success.
   * @throws Exception if any task fails.
   */
  suspend fun run(): Int {
    var successfulTasks = 0
    httpClient.webSocket(method = HttpMethod.Get, host = "127.0.0.1", port = port, path = "/ws/${user.id}") {
      prologueTasks.forEach { it.run(this, user) }
      tasksToRun.forEach { it.setup(this, user) }

      for (i in 0..<operationsRepetitions) {
        tasksToRun.forEach {
          if (it.run(this, user)) {
            successfulTasks++
          }
        }
      }
    }
    return successfulTasks
  }

  fun close() {
    httpClient.close()
  }

  class Builder(
    private val port: Int,
    userId: String,
    private val operationsRepetitions: Int,
    private val httpClient: HttpClient
  ) {
    private val user = User(userId)
    private val prologueTasks: MutableList<ClientTask> = mutableListOf()
    private val tasksToRun: MutableList<ClientTask> = mutableListOf()

    fun addPrologueTask(task: ClientTask): Builder {
      prologueTasks.add(task)
      return this
    }

    fun addTaskToRun(task: ClientTask): Builder {
      tasksToRun.add(task)
      return this
    }

    fun build(): Client {
      return Client(httpClient, port, user, operationsRepetitions, prologueTasks, tasksToRun)
    }
  }
}

internal fun createHttpClient(): HttpClient = HttpClient(CIO) {
  engine {

  }
  install(WebSockets) {
    contentConverter = KotlinxWebsocketSerializationConverter(serializationFormat)
  }
}
