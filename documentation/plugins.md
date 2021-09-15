# Plugins for the Renaissance benchmarking suite

The suite provides hooks for plugins which can subscribe to events related to
harness state and benchmark execution.

A plugin is a user-defined class which must implement the `Plugin` marker interface
and provide at least a default (parameter-less) constructor.
However, such a minimal plugin would not receive any notifications. To receive
notifications, the plugin class must implement interfaces from the `Plugin`
interface name space depending on the type of events it wants to receive, or services it wants
to provide. This is demonstrated in the following example:

```scala
class SimplePlugin extends Plugin
  with AfterHarnessInitListener
  with AfterOperationSetUpListener
  with BeforeOperationTearDownListener {

  override def afterHarnessInit() = {
    // Initialize the plugin after the harness finished initializing
  }

  override def afterOperationSetUp(benchmark: String, index: Int) = {
    // Notify the tool that the measured operation is about to start.
  }

  override def beforeOperationTearDown(benchmark: String, index: Int) = {
    // Notify the tool that the measured operations has finished.
  }
}
```

## Listeners

The following interfaces provide common (paired) event types which allow a plugin to hook
into a specific point in the benchmark execution sequence. They are analogous to common
annotations known from testing frameworks such as JUnit. Harness-level events occur only
once per the whole execution, benchmark-level events occur once for each benchmark
executed, and operation-level events occur once for each execution of the measured
operation.

- `AfterHarnessInitListener`, `BeforeHarnessShutdownListener`
- `BeforeBenchmarkSetUpListener`, `AfterBenchmarkTearDownListener`
- `AfterBenchmarkSetUpListener`, `BeforeBenchmarkTearDownListener`
- `AfterOperationSetUpListener`, `BeforeOperationTearDownListener`

The following interfaces provide special non-paired event types:

- `MeasurementResultListener`, intended for plugins that want to receive
measurements results (perhaps to store them in a custom format). The harness calls the
`onMeasurementResult` method with the name of the metric and its value, but only if the
benchmark operation produces a valid result.
- `BenchmarkFailureListener`, which indicates that the benchmark execution
has either failed in some way (the benchmark triggered an exception), or that the benchmark
operation produced a result which failed validation. This means that no measurements results
will be received.

## Services

And the following interfaces are used by the harness to request
services from plugins:

- `MeasurementResultPublisher`, intended for plugins that want to collect
values of additional metrics around the execution of the benchmark operation. The harness
calls the `onMeasurementResultsRequested` method with an instance of event dispatcher which
the plugin is supposed to use to notify other result listeners about custom measurement results.
- `ExecutionPolicy`, intended for plugins that want to control the execution
of the benchmark's measured operation. Such a plugin should implement other interfaces to
get enough information to determine, per-benchmark, whether to execute the measured operation
or not. The harness calls the `canExecute` method before executing the benchmark's measured
operation, and will pass the result of the `isLast` method to some other events.

## Arguments

A plugin that wants to receive command line arguments (via `--with-arg`) must define
a constructor which takes an array of strings (`String[]`) or a string vararg
(`String...`) as parameter. The harness tries to use this constructor first and falls back
to the default (parameter-less) constructor.


## Packaging

The plugin shall be packaged in a standard JAR, the interface classes (e.g. `Plugin`)
are provided by the suite and shall not be part of the plugin JAR.

The main class of the plugin shall be specified as a `Renaissance-Plugin` property inside
`META-INF/MANIFEST.MF` of the plugin JAR.
