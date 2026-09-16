# jmx-metrics plugin for Renaissance suite

This plugin collects a chosen subset of common JMX-derived metrics:
- memory consumption via [MemoryMXBean](https://docs.oracle.com/en/java/javase/11/docs/api/java.management/java/lang/management/MemoryMXBean.html)
and [MemoryPoolMXBean](https://docs.oracle.com/en/java/javase/11/docs/api/java.management/java/lang/management/MemoryPoolMXBean.html),
- garbage collection via [GarbageCollectorMXBean](https://docs.oracle.com/en/java/javase/11/docs/api/java.management/java/lang/management/GarbageCollectorMXBean.html),
- compilation time via [CompilationMXBean](https://docs.oracle.com/en/java/javase/11/docs/api/java.management/java/lang/management/CompilationMXBean.html),
- CPU/process time via [OperatingSystemMXBean](https://docs.oracle.com/en/java/javase/11/docs/api/java.management/java/lang/management/OperatingSystemMXBean.html)
and the platform-specific [com.sun.management.OperatingSystemMXBean](https://docs.oracle.com/en/java/javase/11/docs/api/jdk.management/com/sun/management/OperatingSystemMXBean.html) (where available), and
- total bytes allocated by threads via [com.sun.management.ThreadMXBean.getTotalThreadAllocatedBytes()](https://docs.oracle.com/en/java/javase/21/docs/api/jdk.management/com/sun/management/ThreadMXBean.html#getTotalThreadAllocatedBytes())
(where the running JVM supports it, it was added in JDK 21),
- live/peak/daemon/started thread counts and current-thread CPU/user time via
[ThreadMXBean](https://docs.oracle.com/en/java/javase/11/docs/api/java.management/java/lang/management/ThreadMXBean.html),
- JVM start time and uptime via [RuntimeMXBean](https://docs.oracle.com/en/java/javase/11/docs/api/java.management/java/lang/management/RuntimeMXBean.html), and
- live and cumulative loaded/unloaded class counts via [ClassLoadingMXBean](https://docs.oracle.com/en/java/javase/11/docs/api/java.management/java/lang/management/ClassLoadingMXBean.html).

It supersedes the older [jmx-memory](../jmx-memory) and [jmx-timers](../jmx-timers)
plugins, which remain in this repository for reference. The metrics those
plugins reported can be reproduced using the `legacy:` key (see below),
so that this plugin can be used without changing the downstream data
processing pipeline. Every metric produced by this plugin has to be
asked for (opt-in), nothing is reported otherwise.

## Building

To build the plugin run the following command:

```shell
../../tools/sbt/bin/sbt assembly
```

The plugin will be available as `target/plugin-jmxmetrics-assembly-VER.jar`.
It is built to run on Java 11+. Capabilities that only exist on newer JVMs
(e.g, total thread-allocated bytes) are probed once when the plugin
starts and omitted where unavailable.

## Using the plugin

To use the plugin, add it with the `--plugin` option when starting the suite,
along with at least one of the argument keys below (with no arguments, the
plugin reports nothing). An output file is given below because these
metrics are not printed to standard output.

```shell
java renaissance-gpl-0.16.1.jar \
  --plugin plugin-jmxmetrics-assembly-0.9.0.jar \
  --with-arg mem:all --with-arg gc:all --with-arg jit:all \
  --json results.json \
  ...
```

### Plugin arguments

Each structured argument is passed through the `--with-arg` mechanism of
the Renaissance harness in the form `key:token,token,...`.

Within the value of a key, each comma-separated entry is one of:
- a plain `token` — reports its base (current) value only;
- `token@base` — reports the base value only, same as a plain token, but
  explicitly, so that a wildcard (below) leaves it alone;
- `token@delta` — reports **only** the delta (the difference between values
  sampled immediately before and after the measured operation), not the
  base, e.g. `time@delta`;
- `token@both` — reports **both** the base value and its delta, e.g. `time@both`;
- a plain wildcard `@base`, `@delta`, or `@both` (no token before it) — fills
  in that state for every token this key already selected from other
  entries in the same argument that carries no annotation of its own, e.g.
  `gc:count,time,@delta` reports only the two deltas, no base values at all.

A wildcard only fills in a default for tokens that weren't already given
their own explicit annotation — including an explicit `@base` — and it does
so regardless of where it appears in the list. E.g. `gc:count@both,time,@delta`
reports both base and delta for `count` (its own `@both` wins), while `time`
is swept into delta-only by the wildcard. With more than one plain wildcard
for the same key, the last one given wins.

`all` composes with these forms: `key:all` reports the base value of every
metric of that key (delta is never implied by `all` alone); `key:all@both`
reports base and delta for every metric; `key:all@delta` reports delta only,
for every metric, with no base values at all; `key:all@base` reports base
only, explicitly, so that a later wildcard for the same key leaves every
metric of it alone.

A plain, unannotated `delta` on its own is not valid and is rejected with a
warning — it must annotate a token (or appear as a plain wildcard `@delta`).

The following keys are supported:

- **`mem:used,nonheap-used`** — overall JVM memory usage from `MemoryMXBean`.
  `used` is heap memory used (the common case); `nonheap-used` is the
  non-heap equivalent, requested separately since it's needed far less
  often. Each is annotated independently, e.g. `mem:used,nonheap-used@both`
  reports base only for heap-used but base and delta for non-heap-used.
- **`gc:count,time`** — collection count/time for *every* garbage collector
  MXBean present, under its own name. `count` and `time` are annotated
  independently, e.g. `gc:count@both,time` reports delta (and base) for
  count, base only for time.
- **`mempool:used,peak,nonheap-used,nonheap-peak,reset-peaks`** — current
  usage and/or peak usage of every heap or non-heap memory pool. `used` and
  `peak` are heap-flavored (the common case); `nonheap-used`/`nonheap-peak`
  are their non-heap counterparts. All four are annotated independently,
  e.g. `mempool:peak@both` reports how much the peak grew during the
  measured operation, alongside its current value, while
  `mempool:nonheap-peak@delta` reports only the growth of the non-heap peak,
  with no base value at all. `reset-peaks` resets peak usage at the start
  of every repetition, so that the peak reflects the high-water mark
  reached during that repetition (without it, peak usage accumulates over
  the whole benchmark run instead); it is a plain behavior toggle,
  independent of `all`, and cannot itself be annotated.
- **`thread:count,daemon-count,peak-count,started-count,cpu-time,user-time,alloc`** —
  live/peak/daemon/started thread counts and current-thread CPU/user time,
  from the portable `ThreadMXBean` interface, plus total bytes allocated
  across all threads (part of the platform-specific interface since Java
  21). All six are annotated independently, e.g.
  `thread:peak-count@both,count` reports base and delta for the peak count,
  base only for the live count. `cpu-time`/`user-time`
  measure whichever thread calls into the management interface of the JVM
  to take the reading — the harness thread driving the operations of the
  benchmark, not necessarily every thread that does work during the
  measured operation; treat them with that scope in mind, especially for
  benchmarks that spawn their own worker threads. `reset-peaks` resets the
  peak thread count at the start of every operation, so that the peak
  reflects the high-water mark reached during that operation (without it,
  peak count is whatever peak-since-start value the JVM tracks on its own);
  like `reset-peaks` for `mempool:`, it is a plain behavior toggle,
  independent of `all`, and cannot itself be annotated.
- **`jit:time`** — total JIT compilation time. `time` is the cumulative
  total since JVM start; `delta` annotates it directly, giving the time
  spent compiling during the measured operation.
- **`os:load-average,processors,process-time,system-load,process-load`** —
  system load average and available-processor count (portable, from
  `OperatingSystemMXBean`), plus process CPU time and system/process CPU
  load (platform-specific, from `com.sun.management.OperatingSystemMXBean`;
  omitted with a warning where that extended interface isn't available).
  Each of the five is annotated independently, e.g.
  `os:system-load@both,load-average` reports base and delta for
  system-load but base only for load-average, without forcing delta onto
  any of the other three.
- **`runtime:vm-start-time,vm-uptime`** — JVM start time and uptime from
  `RuntimeMXBean`, both in milliseconds since the epoch/since start
  respectively. Each is annotated independently, e.g.
  `runtime:vm-uptime@both` reports base and delta for uptime (the delta is
  the wall-clock time elapsed during the measured operation, as measured
  internally by this bean); the delta of `vm-start-time` is always `0`
  once the JVM has started, since it never changes.
- **`class:live-count,total-loaded-count,total-unloaded-count`** — the
  number of classes currently loaded, and the cumulative-since-start totals
  of classes loaded and unloaded, from `ClassLoadingMXBean`. Each is
  annotated independently, e.g. `class:live-count@both` reports base and
  delta for the live count (the delta reflects classes loaded and unloaded
  during the measured operation, and can be negative);
  `total-loaded-count`/`total-unloaded-count` are cumulative since JVM
  start, so their deltas are never negative.
- **`legacy:memory,timers`** — reproduces the exact metric names and values
  of the old [jmx-memory](../jmx-memory) and [jmx-timers](../jmx-timers)
  plugins, so an existing data-processing pipeline built around those names
  can keep working unchanged. Unlike every other key, `legacy:` supports no
  annotation at all (`legacy:memory@both` is rejected) since the
  underlying values were always reported both ways, unconditionally;
  `legacy:all` selects both `memory` and `timers`.

An argument key given with no recognized tokens (e.g. a plain `gc:` or a
key with only unrecognized tokens) selects no metrics and prints a warning.
An entirely unrecognized key, token, or annotation also produces a warning,
but does not stop the plugin from starting.

## Results

The results in the JSON file will have the following form, one group of
metrics per argument key given.

### `mem:` metrics

```json
{
  "jmx_mem_heap_used_bytes": 2793149376,
  "jmx_mem_heap_used_bytes_delta": 1337913688,
  "jmx_mem_nonheap_used_bytes": 52428800,
  "jmx_mem_nonheap_used_bytes_delta": 14464
}
```

### `gc:` metrics

One group per collector present, with the collector name
embedded in the metric names:

```json
{
  "jmx_gc_g1_young_generation_collection_count": 94,
  "jmx_gc_g1_young_generation_collection_count_delta": 6,
  "jmx_gc_g1_young_generation_collection_time_ms": 11,
  "jmx_gc_g1_young_generation_collection_time_ms_delta": 1,
  "jmx_gc_g1_old_generation_collection_count": 2,
  "jmx_gc_g1_old_generation_collection_count_delta": 0,
  "jmx_gc_g1_old_generation_collection_time_ms": 0,
  "jmx_gc_g1_old_generation_collection_time_ms_delta": 0
}
```

### `mempool:` metrics

One group per pool present matching the requested categories:

```json
{
  "jmx_mempool_heap_g1_eden_space_used_bytes": 134217728,
  "jmx_mempool_heap_g1_eden_space_used_bytes_delta": 67108864,
  "jmx_mempool_heap_g1_eden_space_peak_bytes": 201326592,
  "jmx_mempool_nonheap_metaspace_used_bytes": 52428800,
  "jmx_mempool_nonheap_metaspace_used_bytes_delta": 0,
  "jmx_mempool_nonheap_metaspace_peak_bytes": 52428800
}
```

### `thread:` metrics

```json
{
  "jmx_thread_count": 24,
  "jmx_thread_daemon_count": 18,
  "jmx_thread_peak_count": 27,
  "jmx_thread_started_count": 142,
  "jmx_thread_current_cpu_time_ns": 48123456,
  "jmx_thread_current_user_time_ns": 41120000,
  "jmx_thread_total_allocated_bytes": 4213988352,
  "jmx_thread_total_allocated_bytes_delta": 1358027264
}
```

`jmx_thread_total_allocated_bytes` is only present where the running JVM
computes a real total (a warning is printed and the metric omitted
otherwise); as of this writing that requires JDK 21+ on most vendors' JDKs,
though some vendors backport it to earlier LTS lines. Where supported but
not already enabled, the plugin enables it at startup.
`jmx_thread_current_cpu_time_ns`/`jmx_thread_current_user_time_ns` are only
present where the running JVM supports current-thread CPU time measurement
(a warning is printed and both omitted otherwise); where supported but
not already enabled, the plugin enables it at startup.

### `runtime:` metrics

```json
{
  "jmx_runtime_vm_start_time_ms": 1732000000000,
  "jmx_runtime_vm_uptime_ms": 154237,
  "jmx_runtime_vm_uptime_ms_delta": 1173
}
```

### `class:` metrics

```json
{
  "jmx_class_live_count": 8213,
  "jmx_class_total_loaded_count": 8217,
  "jmx_class_total_unloaded_count": 4
}
```

### `jit:` metrics

```json
{
  "jmx_jit_total_compilation_time_ms": 5737,
  "jmx_jit_total_compilation_time_ms_delta": 223
}
```

### `os:` metrics

```json
{
  "jmx_os_system_load_average_x100": 234,
  "jmx_os_available_processors_count": 16,
  "jmx_os_process_cpu_time_ns": 48123456789,
  "jmx_os_system_cpu_load_mpct": 37120,
  "jmx_os_process_cpu_load_mpct": 6120
}
```

`jmx_os_system_load_average_x100` is fixed-point, scaled by 100 (e.g. a
load average of `2.34` is reported as `234`). It is *not* a percentage
(load average is an unbounded count of runnable entities, not a 0..1
fraction), hence the explicit `_x100` scale-factor suffix rather than
`_pct`/`_mpct`. The `_mpct` ("milli-percent") metrics, by contrast, *are*
0..1 fractions and are fixed-point scaled by 100,000 to preserve 3 decimal
places of percentage: divide by 1000 to get percent (e.g. a system CPU
load ratio of `0.3712` is reported as `37120`, i.e. `37.120` percent). A
negative sentinel (`-1`) is preserved as-is where the underlying MXBean
method reports the value as unavailable.

### `legacy:` metrics

`legacy:memory` identifies the young/old generation collector by name
(`G1 Young Generation`/`PS Scavenge`/`Copy` for young, `G1 Old Generation`/
`PS MarkSweep`/`MarkSweepCompact` for old). If a collector matching the
young or old generation cannot be found, the plugin issues a warning at
startup and reports `-1` as the values of the metrics). Compared to the
original `jmx-memory` plugin, running on a JVM with the serial collector
(`Copy`/`MarkSweepCompact`) will report real values instead of `-1`.

```json
{
  "jmx_memory_young_collection_count": 94,
  "jmx_memory_young_collection_delta": 6,
  "jmx_memory_young_collection_total_ms": 254,
  "jmx_memory_young_collection_time_ms": 11,
  "jmx_memory_old_collection_count": 2,
  "jmx_memory_old_collection_delta": 0,
  "jmx_memory_old_collection_total_ms": 93,
  "jmx_memory_old_collection_time_ms": 0,
  "jmx_memory_used_size": 2793149376,
  "jmx_memory_used_delta": 1337913688
}
```

Note the naming: `_total_ms` is the cumulative value and `_time_ms` is the
delta, which matches the names reported by the `jmx-memory` plugin, whereas
the metrics enabled through the non-legacy keys will use the `_delta` suffix.

`legacy:timers` reproduces the compilation times reported by `jmx-timers`:

```json
{
  "jmx_timers_compilation_total_ms": 473,
  "jmx_timers_compilation_time_ms": 6
}
```
