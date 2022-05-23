# jmx-memory plugin for Renaissance suite

This plugin collects information about
memory consumption via [MemoryMXBean](https://docs.oracle.com/javase/7/docs/api/java/lang/management/MemoryMXBean.html).
garbage collection execution via [GarbageCollectorMXBean](https://docs.oracle.com/javase/7/docs/api/java/lang/management/GarbageCollectorMXBean.html).

## Building

To build the plugin run the following command:

```shell
../../tools/sbt/bin/sbt assembly
```

The plugin shall be available as `target/plugin-jmxmemory-assembly-VER.jar`.

## Using the plugin

To use the plugin, simply add it with the `--plugin` option when starting the suite.
Note that we specify an output file as the counters are not visible on the standard output.

```shell
java renaissance-gpl-0.14.1.jar \
  --plugin plugin-jmxmemory-assembly-0.0.1.jar\
  --json results.json \
  ...
```

The results in the JSON file will have the following form.
Note that the totals might be increasing even when the delta
values stay at `0` because some collections may happen between
loops (i.e., outside of the measured operation).

```json
{
  ...
  "data": {
    "BENCHMARK": {
      "results": [
        {
          "duration_ns": 1173575273,
          ...
          "jmx_memory_young_collection_count": 94,
          "jmx_memory_young_collection_delta": 6,
          "jmx_memory_young_collection_time_ms": 11,
          "jmx_memory_young_collection_total_ms": 254,
          "jmx_memory_old_collection_count": 2
          "jmx_memory_old_collection_delta": 0,
          "jmx_memory_old_collection_time_ms": 0,
          "jmx_memory_old_collection_total_ms": 93,
          "jmx_memory_used_delta": 1337913688,
          "jmx_memory_used_size": 2793149376,
        },
        ...
  ...
}
```
