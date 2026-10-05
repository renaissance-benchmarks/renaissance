# Kotlin-Ktor benchmark

The benchmark is designed to simulate a chat application where multiple clients send requests simultaneously.
It uses the [Ktor](https://ktor.io/) framework.

Namely, the benchmark runs multiple clients at the same time.
Each client first sets its own display name once, then is set up with one or both of the following
repeated tasks:

- Join a chat and send a randomized message to it.
- Create a direct chat with another user (if not already created) and send a randomized message to them.

Clients repeat those tasks required number of times specified via `iterations_count` parameter.
For the validation, each successful task completion is counted and compared to the expected number at the end of the
run.

It's also possible to implement validation via end-to-end comparison of the artifacts produced by the run.
An example of such an artifact could be a log file of all sent/received messages or of completed tasks.
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

Here are the parameters that can be passed to the benchmark:

- `port`: Port the server listens on. Default value is 9496.
- `client_count`: Number of clients that are simultaneously sending the requests.
  Increasing number of clients (with a proportional decrease in the number of repetitions) has little effect on the
  overall runtime. Default value is the number of available CPUs.
- `iterations_count`: Number of times clients should repeat their designated tasks. Default value is 2000.
- `chat_count`: How many public chats should be set up for user interactions.
  This simulates interactions in a few large chats.
  Increasing the number of chats will reduce runtime, since it reduces contention between clients.
  Default value is 10.
- `group_message_fraction`: Fraction of clients that send messages to group chats. Default value
  is 1.0.
- `direct_message_fraction`: Fraction of clients that send direct messages. Default value
  is 0.5.
- `random_seed`: Random seed for the whole benchmark run - both client task setup and server-side
  chat id generation are derived from it, for reproducibility. Default value is 32.

## Concurrency model

The common way for concurrent programming in Kotlin is to use coroutines.
The high-level idea of coroutines is that multiple blocking operations may run on the same thread pool.
For more details, please see [the official coroutines guide](https://kotlinlang.org/docs/coroutines-overview.html).
This is exactly what Ktor uses.

`client_count` controls client-side concurrency directly: `KtorRenaissanceBenchmark` builds one thread
pool sized to `min(client_count, availableProcessors)` and runs every client's tasks on the coroutine
scope backed by it.

Server-side concurrency is not controllable this way. This benchmark uses Ktor's CIO application engine,
since the point of the benchmark is to exercise Kotlin-coroutine-native code (Netty, a Java NIO framework,
is already exercised by the `twitter-finagle` benchmark in this suite). As of Ktor 2.3.8, `CIOApplicationEngine`
hardcodes its own dispatcher and ignores the `connectionGroupSize`/`workerGroupSize`/`callGroupSize` settings
it otherwise inherits. Netty uses these settings to size its event loop groups; CIO does not. No parameter
changes the number of threads used on the server side.

Considering there are enough available threads, both server and the client are capable of running mostly concurrently
with a few synchronization points.
Namely, if multiple clients are trying to perform the same operation on the same object
(modifying the message history, chat pool, etc.), it will be processed sequentially.
While operations such as sending a message to the server or routing the message on the server side and sending replies
are parallel (up to contention for the system resources).

It's possible to influence the amount of contention present by adjusting the parameters of the benchmark.
Increasing the number of chats will decrease contention for the modification of the chat history (the opposite is true
as well).
Increasing group/direct message fraction will increase contention for the chat history and the chat pool, respectively.
Increasing the number of clients will increase contention in all synchronization points.

## Core classes overview

- `KtorRenaissanceBenchmark` is the root class which initialises, runs and tears down the server and the clients.
  See [Running the benchmark](#running-the-benchmark) for more details on the available parameters for client and server
  setup.
- `ChatApplication` is the class which sets up the Ktor application for the `ChatServer`.
  Namely, it installs the required plugins, such as `WebSockets`, and sets up routes from websockets calls to the server operations.
- `ChatServer` is the class which handles the server side logic for the chat application. It is responsible for
  maintaining the state of the chat application, such as the list of users, the list of chats, and the messages sent in
  the chats. It also handles the logic for the different operations that the clients can perform, such as joining a
  chat, sending a message, and sending a direct message. Important detail is that the server will broadcast the message
  which is sent to some chat. So, if the user sends a message to the chat, they will receive the message back, and
  that's how they'll know that the 'transaction' was successful. Chat ids and the initial set of chats are generated
  from the benchmark's own seeded random generator, and `ChatServer` resets its state back to that same initial set at
  the start of every repetition, so repetitions run against comparable starting conditions.
- `ClientManager` sets up clients according to the parameters received from the `KtorRenaissanceBenchmark`, runs them,
  and tears them down.
- `Client` represents one simulated user: a shared `User` identity plus a collection of tasks. A one-time prologue task
  runs first (setting the display name), then the regular tasks are run sequentially for the required number of times.
- `ClientTask` is the interface which represents a task that a client can perform.
  There are currently three types of client tasks:
    - `RenameClientTask`, a prologue task that sets the client's display name once, at the start of the session.
    - `JoinGroupAndSendMessageClientTask`, which joins a chat and sends a message to it.
    - `DirectMessageClientTask`, which creates (or reuses) a direct chat with another user and sends a message to it.
- `Command` instances and `Message` are the data classes with which client and server communicate with each other. Both
  classes are being sent as JSON objects.