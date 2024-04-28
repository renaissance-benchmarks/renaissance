# Kotlin-Ktor benchmark

The benchmark is designed to simulate a chat application where multiple clients send requests simultaneously.
It uses the [Ktor](https://ktor.io/) framework.

Namely, the benchmark runs multiple clients at the same time.
Clients are set up with one or both of the following tasks:

- Join a chat and send a randomized message to it.
- Create a private chat with another user (if not already created) and send a randomized message to them.

They repeat those task the required number of times.
After that number of successfully completed tasks is validated.

It's also possible to implement validation via end-to-end comparison of the artifacts is produced.
However, in our case it would be tricky to implement, since every run is randomized both in content and in the order of
operations, so a semantic comparison of logs would be required.
Gladly, it's not needed for us, since each task auto-validates itself, so it will successfully terminate only if
everything went as expected.
Hence, counting the number of successfully completed tasks is enough to validate the run.

## Running the benchmark

To run benchmark, execute the following command:

```bash
java -jar <renaissance.jar> kotlin-ktor
```

Here are the arguments that can be passed to the benchmark:

- `client_count`: Number of clients that are simultaneously sending the requests.
  Increasing number of clients (with proportional decrease in number of repetitions) doesn't have much effect on the
  overall runtime. Default value is the number of available CPUs.
- `iterations_count`: Number of times clients should repeat their designated operations. Default value is 2000.
- `chat_count`: How many public chats should be setup for user interactions. This simulates interactions in a few
  large chats. Increasing number of chats will reduce runtime, since it reduces contention between clients. Default
  value is 10.
- `group_message_fraction`: Fraction of clients which execute joinChatAndSendMessage. Default value
  is 1.0.
- `private_message_fraction`: Fraction of clients that should send private messages. Default value
  is 0.5.
- `random_seed`: Random seed to use for client tasks setup for reproducibility. Default value is 32.

## Concurrency model

The common way for concurrent programming in Kotlin is to use coroutines.
The high-level idea is that you of coroutines is that multiple blocking operations may run on the same thread pool.
For more details, please see [the official coroutines guide](https://kotlinlang.org/docs/coroutines-overview.html)
This is exactly what Ktor uses.

Unfortunately, the Ktor framework does not provide a way neither to limit the number of threads used for internal
operations nor to have separate thread pools for the client and server operations.
Ktor, mostly uses the `Dispatchers.IO`and `Dispatchers.Default`, which operate on intersecting thread pools.
The `Dispatchers.Default` has a thread pool of size equal to number of CPU cores, but it's at least 2.
The `Dispatchers.IO` is a bit more complicated.
By default, it has a thead pool of size 64 (which could be controlled via a system
property`kotlinx.coroutines.io.parallelism`).
However, it's possible to obtain a separate view of the `Dispatchers.IO` by using
`Dispatchers.IO.limitedParallelism(n)`, which may create up to `n` additional threads.
In theory the usage of the `Dispatchers.IO` should be reserved for IO-bound operations and the `Dispatchers.Default`
should be used for CPU-bound operations.
However, in practice, these rules are rather semantic and cannot and are not enforced by coroutines.
So, Ktor may switch between these two dispatchers as it sees fit, with potential changes in the future versions.

With this mind, we start the server using `start` method.
To make sure that Ktor internal operations don't interfere much with us starting client jobs,
we use a separate thread pool to start clients, though internally Ktor will switch to another thread pool.

Considering there are enough available threads, both server and the client are capable of running mostly concurrently
with a few synchronization points.
Namely, if multiple clients are trying to perform the same operation on the same object
(modifying the message history, chat pool, etc.), it will be processed sequentially.
While operations such as sending a message to the server or routing the message on the server side and sending replies
are parallel (up to contention for the system resources).

It's possible to influence the amount of contention present by adjusting the parameters of the bencmark.
Increasing the number of chats will decrease contention for the modification of the chat history (the opposite is true
as well).
Increasing group/private message fraction will increase contention for the chat history and the chat pool, respectively.
Increasing the number of clients will increase contention in all synchronization points.

## Core classes overview

- `KtorRenaissanceServer` is the root class which initialises, runs and tears down the server and the clients.
  See [Running the benchmark](#running-the-benchmark) for more details on the availiable arguments for client and server
  setup.
- `ChatApplication` is the class which sets up the Ktor application for the `ChatServer`. Namely it installs the
  required plugins, such as `WebSockets`, and sets up routes from websockets calls to the server operations.
- `ChatServer` is the class which handles the server side logic for the chat application. It is responsible for
  maintaining the state of the chat application, such as the list of users, the list of chats, and the messages sent in
  the chats. It also handles the logic for the different operations that the clients can perform, such as joining a
  chat, sending a message, and sending a private message. Important detail is that the server will broadcast the message
  which is sent to some chat. So, if the user sends a message to the chat, they will receive the message back and that's
  how they'll now that the 'transaction' was successful.
- `ClientManager` sets up clients according to the arguments received from the `KtorRenaissanceBenchmark`, runs them,
  and tears them down.
- `Client` is essentially represents a collection of tasks which are run sequentially for the required number of times.
- `ClientTask` is the interface which represents a task that a client can perform. So far the are 2 types of client
  tasks:
    - `GroupMessageTask` which represents the task of joining a chat and sending a message to it.
    - `PrivateMessageTask` which represents the task of sending a private message to another user.
- `Command` instances and `Message` are the data classes with which client and server communicate with each other. Both
  classes are being send as JSON objects.