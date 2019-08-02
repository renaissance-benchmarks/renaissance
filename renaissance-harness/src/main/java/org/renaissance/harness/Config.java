package org.renaissance.harness;

import org.renaissance.Plugin;
import org.renaissance.Plugin.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

final class Config {

  final List<String> benchmarkSpecifiers = new ArrayList<>();

  int repetitions = -1;
  int runSeconds = 240;
  final List<Plugin> plugins = new ArrayList<>();

  ExecutionPolicyFactory policyFactory = ExecutionPolicyFactory.FIXED_OP_COUNT;
  String policyModule;

  final List<HarnessInitListener> harnessInitListeners = new ArrayList<>();
  final List<HarnessShutdownListener> harnessShutdownListeners = new ArrayList<>();
  final List<BenchmarkSetUpListener> benchmarkSetUpListeners = new ArrayList<>();
  final List<BenchmarkTearDownListener> benchmarkTearDownListeners = new ArrayList<>();
  final List<OperationSetUpListener> operationSetUpListeners = new ArrayList<>();
  final List<OperationTearDownListener> operationTearDownListeners = new ArrayList<>();
  final List<BenchmarkResultListener> benchmarkResultListeners = new ArrayList<>();
  final List<BenchmarkFailureListener> benchmarkFailureListeners = new ArrayList<>();

  boolean printList = false;
  boolean printRawList = false;
  boolean printGroupList = false;

  String configuration = "default";


  public Config withBenchmarkSpecification(String v) {
    benchmarkSpecifiers.addAll(
      Arrays.stream(v.split(",")).collect(Collectors.toList())
    );

    return this;
  }

  public Config withPlugin(String pluginModule) {
    plugins.addAll(Arrays.stream(pluginModule.split(","))
      .map(n -> {
        try {
          return (Plugin) Class.forName(pluginModule).newInstance();
        } catch (Throwable e) {
          throw new RuntimeException(e);
        }
      })
      .collect(Collectors.toList())
    );

    return this;
  }

  public Config withRepetitions(int repetitions) {
    this.policyFactory = ExecutionPolicyFactory.FIXED_OP_COUNT;
    this.repetitions = repetitions;
    return this;
  }

  public Config withWallClockRunSeconds(int runSeconds) {
    this.policyFactory = ExecutionPolicyFactory.FIXED_TIME;
    this.runSeconds = runSeconds;
    return this;
  }

  public Config withOperationRunSeconds(int runSeconds) {
    this.policyFactory = ExecutionPolicyFactory.FIXED_OP_TIME;
    this.runSeconds = runSeconds;
    return this;
  }

  public Config withPolicy(String policyModule) {
    this.policyFactory = ExecutionPolicyFactory.CUSTOM;
    this.policyModule = policyModule;
    return this;
  }

  public Config withResultWriter(ResultWriter writer) {
    harnessShutdownListeners.add(writer);
    benchmarkResultListeners.add(writer);
    benchmarkFailureListeners.add(writer);
    return this;
  }

  public Config withList() {
    printList = true;
    return this;
  }

  public Config withRawList() {
    printRawList = true;
    return this;
  }

  public Config withGroupList() {
    printGroupList = true;
    return this;
  }

  public Config withConfiguration(String configuration) {
    this.configuration = configuration;
    return this;
  }
}
