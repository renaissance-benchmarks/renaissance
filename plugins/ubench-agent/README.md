# ubench-agent plugin for Renaissance suite

This plugin collects values of arbitrary hardware performance counters.
It uses a [microbenchmarking agent](https://github.com/d-iii-s/java-ubench-agent)
to access the counters through [PAPI](https://icl.utk.edu/papi/).

## Building

To build the plugin, you also need to build the native agent for JVM.
Start by building the agent:

```shell
./build-ubench-agent.sh
```

This will fetch a supported version of the agent and build the shared
library (it will also print a path to it to pass to JVM).

Then continue building the plugin itself:

```shell
../../tools/sbt/bin/sbt assembly
```

The plugin shall be available as `target/plugin-ubenchagent-assembly-VER.jar`.

## Using the plugin

To use the plugin, you need to add the native agent to the JVM and register
the plugin with the Renaissance suite (update the path according to your setup,
i.e., whether you have built the suite and/or the agent yourself).
Specify the events as a plugin argument.
Note that we specify an output file as the counters are not visible on the
standard output.

```shell
java -agentpath:libubench-agent.so-jar -jar renaissance-gpl-0.14.1.jar \
  --plugin plugin-ubenchagent-assembly-0.0.1.jar --with-arg PAPI_L1_DCM,PAPI_L2_DCM \
  --json results.json \
  ...
```

The results in the JSON file will have the following form:

```json
{
  ...
  "data": {
    "BENCHMARK": {
      "results": [
        {
          "duration_ns": 3693019,
          ...
          "ubench_agent_PAPI_L1_DCM": 171866,
          "ubench_agent_PAPI_L2_DCM": 410758
        },
        ...
  ...
}
```
