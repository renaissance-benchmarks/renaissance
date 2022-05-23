# jmx-timers plugin for Renaissance suite

This plugin collects information about JIT compilation times via
[CompilationMXBean](https://docs.oracle.com/javase/7/docs/api/java/lang/management/CompilationMXBean.html).

## Building

To build the plugin run the following command:

```shell
../../tools/sbt/bin/sbt assembly
```

The plugin shall be available as `target/plugin-jmxtimers-assembly-VER.jar`.

## Using the plugin

To use the plugin, simply add it with the `--plugin` option when
starting the suite.
Note that we specify an output file as the counters are not visible on the
standard output.

```shell
java renaissance-gpl-0.14.1.jar \
  --plugin plugin-jmxtimers-assembly-0.0.1.jar\
  --json results.json \
  ...
```

The results in the JSON file will have the following form.
Note that the `total` might be increasing even when the per-loop
time stays at `0` because some compilation may happen between loops
(i.e., outside of the measured operation).

```json
{
  ...
  "data": {
    "BENCHMARK": {
      "results": [
        {
          "duration_ns": 3693019,
          ...
          "jmx_timers_compilation_time_ms": 6,
          "jmx_timers_compilation_total_ms": 473,
        },
        ...
  ...
}
```
