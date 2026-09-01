package org.renaissance.kotlin.ktor.server

import io.ktor.websocket.*
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.channels.ClosedSendChannelException
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.isActive
import org.renaissance.kotlin.ktor.common.Chat
import org.renaissance.kotlin.ktor.common.DirectMessageChat
import org.renaissance.kotlin.ktor.common.Message
import org.renaissance.kotlin.ktor.common.User
import org.renaissance.kotlin.ktor.common.getRandomDigits
import java.io.IOException
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CopyOnWriteArrayList
import java.util.concurrent.atomic.AtomicInteger
import kotlin.random.Random

const val MAX_MESSAGE_HISTORY_LENGTH = 100
const val MAX_USERNAME_LENGTH = 50

/**
 * This class is in charge of the chat server logic.
 * It contains handlers for events and commands to send messages to specific users on the server.
 * The [chats], [users] and [userSockets] maps are replaced on each benchmark repetition
 * to release the backing table (clearing maps or removing entries does not shrink them).
 */
class ChatServer(initialChatCount: Int, initialSeed: Long) {

  /**
   * Set of initial chat IDs the server starts with. Does not change between repetitions.
   */
  private val initialChatIds = Random(initialSeed).generateChatIds(initialChatCount)

  /**
   * The atomic counter used to get unique usernames based on the maximum users the server had.
   */
  private val usersCounter = AtomicInteger()

  /**
   * A concurrent map associating session IDs with [User] instances.
   */
  private lateinit var users: ConcurrentHashMap<String, User>

  /**
   * A concurrent map associating chat IDs with [Chat] instances.
   */
  internal lateinit var chats: ConcurrentHashMap<String, Chat> private set


  /**
   * Associates a session ID to a collection of websockets.
   * A user can open multiple tabs or windows with same cookies and thus the
   * same session, so there may be several opened sockets for the same client.
   */
  private lateinit var userSockets: ConcurrentHashMap<String, MutableList<WebSocketSession>>

  fun setup() {
    usersCounter.set(0)
    users = ConcurrentHashMap()
    userSockets = ConcurrentHashMap()
    chats = createChats(initialChatIds)
  }

  fun teardown() {
    chats = ConcurrentHashMap(0)
    users = ConcurrentHashMap(0)
    userSockets = ConcurrentHashMap(0)
  }

  private fun createChats(ids: Set<String>): ConcurrentHashMap<String, Chat> =
    ids.associateWithTo(ConcurrentHashMap(ids.size)) { id -> Chat(id) }

  private fun Random.generateChatIds(count: Int): Set<String> =
    generateSequence { nextChatId() }.distinct().take(count).toSet()

  private fun Random.nextChatId(): String = getRandomDigits(base = 16, length = 16)

  /**
   * Handles that a member is identified by a session ID and a socket joined.
   */
  fun registerUser(userId: String, socket: WebSocketSession) {
    // Checks if this user is already registered in the server and gives him/her a temporary name if required.
    users.computeIfAbsent(userId) {
      val user = User(userId)
      user.name = "user${usersCounter.incrementAndGet()}"
      user
    }

    // Associates this socket to the member ID.
    // Since iteration is likely to happen more frequently than adding new items,
    // we use a `CopyOnWriteArrayList`.
    val list = userSockets.computeIfAbsent(userId) { CopyOnWriteArrayList() }
    list.add(socket)
  }

  suspend fun joinChat(chatId: String, userId: String) {
    val chat = chats[chatId]!!
    val user = users[userId]!!
    // Only when joining the first socket for a member notifies the rest of the users.
    if (chat.users.add(user) && userSockets[userId]?.size == 1) {
      chats[chatId]?.broadcast("Member joined: ${user.name}")
      userSockets[userId]?.forEach {
        it.send("You've joined chat $chatId")
        it.send("Last messages:")
        chat.lastMessages.forEach { message ->
          it.send(message)
        }
      }
    }
  }

  /**
   * Handles a [userId] requesting change of the display name to [newName].
   * Responses are sent to all socket sessions.
   */
  suspend fun renameUser(userId: String, newName: String) {
    if (newName.isBlank())
      return sendTo(userId, "server::rename::help", "/user [newName]")

    if (newName.length > MAX_USERNAME_LENGTH)
      return sendTo(userId, "server::rename::error", "new name is too long: 50 characters limit")

    val user = users[userId] ?: return
    val oldName = user.rename(newName) ?: return

    sendTo(userId, "server::rename", "You have been renamed from $oldName to $newName")
  }

  /**
   * Handles that a [userId] with a specific [socket] left the server.
   */
  suspend fun disconnectUserSocket(userId: String, socket: WebSocketSession) {
    // Removes the socket connection for this member
    val connections = userSockets[userId] ?: return
    connections.remove(socket)
    if (connections.isEmpty()) {
      // If there are no more connections for this member, we remove it from the server.
      userSockets.remove(userId) ?: return
      val user = users.remove(userId) ?: return

      usersCounter.decrementAndGet()

      // If the member was in a chat, we notify the rest of the members about this event.
      user.let { userInChat ->
        chats.values.forEach { chat ->
          if (chat.users.remove(userInChat)) {
            chat.broadcast("Member left: ${userInChat.name}")
          }
        }
      }
    }
  }

  /**
   * Handles sending to a [recipientUserId] from a [senderUserId] a [message].
   *
   * Both [recipientUserId] and [senderUserId] are identified by its session-id.
   */
  suspend fun sendTo(recipientUserId: String, senderUserId: String, message: String) {
    userSockets[recipientUserId]?.sendToEach(Frame.Text("[$senderUserId] $message"))
  }

  /**
   * Handles a [message] sent from a [userId] by notifying the rest of the users.
   */
  suspend fun sendMessage(userId: String, message: Message) {
    // Pre-format the message to be send, to prevent doing it for all the users or connected sockets.
    val userName = users[userId]?.name ?: userId
    val formatted = "[$userName] ${message.content}"

    // Sends this pre-formatted message to all the members in the server.
    val chat = chats[message.chatId] ?: return

    chat.broadcast(formatted)

    val lastMessages = chat.lastMessages
    // Appends the message to the list of [lastMessages] and caps that collection to 100 items to prevent
    // growing too much.
    lastMessages.addLast(formatted)

    if (lastMessages.size > MAX_MESSAGE_HISTORY_LENGTH) {
      lastMessages.removeFirst()
    }
  }

  /**
   * Sends a [message] to all the members in the server, including all the connections per member.
   */
  private suspend fun Chat.broadcast(message: String) {
    users.asSequence().mapNotNull { user -> userSockets[user.id] }.forEach { sockets ->
      sockets.sendToEach(Frame.Text(message))
    }
  }

  /**
   * Sends a [frame] to every socket in [this] list. Skips over sockets that are
   * already closed ([ClosedSendChannelException]) or broken ([IOException]), but
   * does not close them (it did not open them). Anything else (a bug, or our own
   * cancellation) is left to propagate. Cancellations need to be handled with care,
   * because we may get a [CancellationException] when a different coroutine cancels
   * the [WebSocketSession] (dropping buffered outgoing messages). That is also
   * skipped, but only if it did not come from our own coroutine being cancelled.
   */
  private suspend fun List<WebSocketSession>.sendToEach(frame: Frame) {
    forEach { session ->
      try {
        session.send(frame.copy())
      } catch (_: ClosedSendChannelException) {
        // already gone; nothing to do here
      } catch (_: IOException) {
        // transport broken; nothing to do here
      } catch (t: CancellationException) {
        if (!currentCoroutineContext().isActive) throw t
        // not our cancellation; nothing to do here
      }
    }
  }

  fun createDirectMessageChat(creatorUserId: String, inviteeUserId: String): String {
    val chat = chats.computeIfAbsent(DirectMessageChat.hashForChat(creatorUserId, inviteeUserId)) {
      DirectMessageChat(
        creatorUserId,
        inviteeUserId,
        it
      ).apply {
        users.add(this@ChatServer.users[creatorUserId]!!)
        users.add(this@ChatServer.users.computeIfAbsent(inviteeUserId) {
          User(inviteeUserId).apply {
            name = "user${usersCounter.incrementAndGet()}"
          }
        })
      }
    }
    return chat.id
  }
}
