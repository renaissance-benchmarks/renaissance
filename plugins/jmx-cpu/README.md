# jmx-cpu plugin for Renaissance suite

This plugin collects information about processor usage 
via [OperatingSystemMXBean](https://docs.oracle.com/javase/8/docs/api/java/lang/management/OperatingSystemMXBean.html).

## Building

To build the plugin run the following command:

```shell
../../tools/sbt/bin/sbt assembly
```

The plugin shall be available as `target/plugin-jmxcpu-assembly-VER.jar`.

## Using the plugin

To use the plugin, simply add it with the `--plugin` option when starting the suite.
Note that we specify an output file as the counters are not visible on the standard output.

```shell
java renaissance-gpl-0.15.0.jar \
  --plugin plugin-jmxcpu-assembly-0.0.1.jar\
  --json results.json \
  ...
```

The results in the JSON file will have the following form.
Note that the totals might be increasing even when the delta
values stay at `0` because some collections may happen between
loops (i.e., outside of the measured operation). 

The `OperatingSystemMXBean` may produce `NaN` values that are interpreted as `0` in the results.
A delta measurement results in `0` if any of the delta values are `NaN`.

```json
{
    ...
    "data": {
        "BENCHMARK": {
            "results": [
            {
                "duration_ns": 589592667,
                ...
                "jmx_cpu_available_processors": 8,
                "jmx_cpu_cpu_load_delta": 7,
                "jmx_cpu_process_cpu_time_delta_ns": 1636691000,
                "jmx_cpu_cpu_load": 93,
                "jmx_cpu_process_load": 88,
                "jmx_cpu_load_average": 3,
                "jmx_cpu_process_load_delta": 7,
                "jmx_cpu_available_processors_delta": 0,
                "jmx_cpu_load_average_delta": 0,
                "jmx_cpu_process_cpu_time_ns": 19644011000
            },
            ...
    ...
}
```
