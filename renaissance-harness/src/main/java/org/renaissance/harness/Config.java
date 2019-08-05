package org.renaissance.harness;

import org.renaissance.Plugin;
import org.renaissance.Plugin.*;
import org.renaissance.core.ModuleLoader;
import org.renaissance.core.ModuleLoader.ModuleLoadingException;

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
    Plugin plugin = null;
    try {
      plugin = ModuleLoader.loadPlugin(pluginModule);
    } catch (ModuleLoadingException e) {
      throw new RuntimeException(e);
    }

    /*
     * Register the plugin into respective listener lists.
     * Note that pair events (setup and teardown) are added to opposite
     * ends of the lists so that each plugin can wrap existing plugins.
     *
     * Therefore it is expected that measurement plugins would be added
     * as the last ones on the command-line.
     */
    plugins.add(plugin);
    if (plugin instanceof HarnessInitListener) {
      harnessInitListeners.add((HarnessInitListener) plugin);
    }
    if (plugin instanceof HarnessShutdownListener) {
      harnessShutdownListeners.add(0, (HarnessShutdownListener) plugin);
    }
    if (plugin instanceof BenchmarkSetUpListener) {
      benchmarkSetUpListeners.add((BenchmarkSetUpListener) plugin);
    }
    if (plugin instanceof BenchmarkTearDownListener) {
      benchmarkTearDownListeners.add(0, (BenchmarkTearDownListener) plugin);
    }
    if (plugin instanceof OperationSetUpListener) {
      operationSetUpListeners.add((OperationSetUpListener) plugin);
    }
    if (plugin instanceof OperationTearDownListener) {
      operationTearDownListeners.add(0, (OperationTearDownListener) plugin);
    }
    if (plugin instanceof BenchmarkResultListener) {
      benchmarkResultListeners.add((BenchmarkResultListener) plugin);
    }
    if (plugin instanceof BenchmarkFailureListener) {
      benchmarkFailureListeners.add((BenchmarkFailureListener) plugin);
    }

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
