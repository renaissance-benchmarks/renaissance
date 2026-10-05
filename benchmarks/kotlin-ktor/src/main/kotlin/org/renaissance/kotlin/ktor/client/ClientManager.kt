package org.renaissance.kotlin.ktor.client

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.CoroutineStart
import kotlinx.coroutines.async
import kotlinx.coroutines.awaitAll
import org.renaissance.kotlin.ktor.KtorRenaissanceBenchmark.Parameters
import org.renaissance.kotlin.ktor.common.SplittableRandom
import org.renaissance.kotlin.ktor.common.getRandomDigits
import kotlin.random.Random

/**
 * Sets up and runs a fixed pool of simulated chat clients.
 *
 * Each call to [setupClients] draws two independent random subsets the client
 * pool - one to receive a group-message task, one to receive a direct-message
 * task - each of size `fraction * numberOfClients`.
 *
 * Both subsets are drawn *without replacement*, meaning that a fraction of
 * `1.0` always selects every client exactly once. The two subsets are drawn
 * independently of each other, so a client can end up with both tasks, one,
 * or none.
 *
 * A direct message's recipient is drawn *with replacement* from the same
 * client pool, including the sender itself: messaging self is treated as an
 * ordinary direct-message chat, which keeps it well-defined even for a
 * single-client pool.
 */
class ClientManager internal constructor(
  private val parameters: Parameters,
  private val coroutineScope: CoroutineScope,
  initialSeed: Long
) {
  private val initialRandom = Random(initialSeed)
  private val setupSeed = initialRandom.nextLong()

  // ArrayList is desired for List.random().
  private val userIds: ArrayList<String> = ArrayList(
    initialRandom.generateUserIds(parameters.clientCount)
  )

  private lateinit var setupRandom: SplittableRandom
  private lateinit var clients: List<Client>

  /**
   * How many client task executions the current [clients] should complete
   * successfully in total, across all repetitions - the number [setupClients]
   * actually assigned, not a value re-derived from raw parameters elsewhere.
   */
  var expectedSuccessfulTaskCount: Int = 0
    private set

  private fun Random.generateUserIds(count: Int): Set<String> =
    generateSequence { nextUserId() }.distinct().take(count).toSet()

  // Length varies so that id strings don't over-specialize length-dependent code paths.
  private fun Random.nextUserId(): String = getRandomDigits(base = 10, length = nextInt(7, 16))

  fun <L> setupClients(availableChatIds: L) where L: Collection<String>, L: RandomAccess {
    setupRandom = SplittableRandom(setupSeed)

    val clientBuilders = userIds.map { userId ->
      Client.Builder(
        parameters.port, userId,
        parameters.clientRepetitionCount,
        createHttpClient()
      ).addPrologueTask(RenameClientTask())
    }

    val groupTaskCount = (userIds.size * parameters.groupMessageFraction).toInt()
    assignRandomTasks(clientBuilders, groupTaskCount, availableChatIds) { chatId, taskRandom ->
      JoinGroupAndSendMessageClientTask(chatId, taskRandom)
    }

    // Picking the self as the recipient is allowed. The server handles
    // messaging self and this remains correct even in a single-user case.
    val directTaskCount = (userIds.size * parameters.directMessageFraction).toInt()
    assignRandomTasks(clientBuilders, directTaskCount, userIds) { recipientUserId, taskRandom ->
      DirectMessageClientTask(recipientUserId, taskRandom)
    }

    expectedSuccessfulTaskCount = (groupTaskCount + directTaskCount) * parameters.clientRepetitionCount

    clients = clientBuilders.map { it.build() }
  }

  private fun <L> assignRandomTasks(
    builders: List<Client.Builder>, count: Int, targets: L,
    createTask: (String, Random) -> ClientTask
  ) where L: Collection<String>, L: RandomAccess {
    // Draw builders without replacement to assign each at most one task.
    // For each task, draw a target with replacement and split off a new
    // Random so that tasks do not share a single thread-unsafe Random.
    builders.shuffled(setupRandom).take(count).forEach { builder ->
      builder.addTaskToRun(createTask(targets.random(setupRandom), setupRandom.split()))
    }
  }

  suspend fun runClients(): Int {
    return clients.map { coroutineScope.async(start = CoroutineStart.LAZY) { it.run() } }
      .map { it.also { it.start() } }
      .awaitAll()
      .sum()
  }

  fun closeClients() {
    clients.forEach { it.close() }
    clients = emptyList()
  }

}
