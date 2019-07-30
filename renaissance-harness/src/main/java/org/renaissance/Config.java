package org.renaissance;

import org.renaissance.harness.Plugin;
import org.renaissance.harness.Plugin.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

final class Config {

  enum ExecutionPolicyType {
    FIXED_COUNT,
    FIXED_TIME,
    CUSTOM;
  }

  final List<String> benchmarkSpecifiers = new ArrayList<>();

  int repetitions = -1;
  int runSeconds = 240;
  final List<Plugin> plugins = new ArrayList<>();

  ExecutionPolicyType policyType = ExecutionPolicyType.FIXED_COUNT;
  String customPolicy;

  final List<HarnessInitListener> harnessInitListeners = new ArrayList<>();
  final List<HarnessShutdownListener> harnessShutdownListeners = new ArrayList<>();
  final List<BenchmarkSetUpListener> benchmarkSetUpListeners = new ArrayList<>();
  final List<BenchmarkTearDownListener> benchmarkTearDownListeners = new ArrayList<>();
  final List<OperationSetUpListener> operationSetUpListeners = new ArrayList<>();
  final List<OperationTearDownListener> operationTearDownListeners = new ArrayList<>();
  final List<ValidResultListener> validResultListeners = new ArrayList<>();
  final List<InvalidResultListener> invalidResultListeners = new ArrayList<>();

  boolean printList = false;
  boolean printRawList = false;
  boolean printGroupList = false;
  boolean functionalTest = false;


  public Config withBenchmarkSpecification(String v) {
    benchmarkSpecifiers.addAll(
      Arrays.stream(v.split(",")).collect(Collectors.toList())
    );

    return this;
  }

  public Config withPlugin(String v) {
    plugins.addAll(Arrays.stream(v.split(","))
      .map(n -> {
        try {
          return (Plugin) Class.forName(v).newInstance();
        } catch (Throwable e) {
          throw new RuntimeException(e);
        }
      })
      .collect(Collectors.toList())
    );

    return this;
  }

  public Config withRepetitions(int repetitions) {
    this.policyType = ExecutionPolicyType.FIXED_COUNT;
    this.repetitions = repetitions;
    return this;
  }

  public Config withRunSeconds(int runSeconds) {
    this.policyType = ExecutionPolicyType.FIXED_TIME;
    this.runSeconds = runSeconds;
    return this;
  }

  public Config withPolicy(String customPolicy) {
    this.policyType = ExecutionPolicyType.CUSTOM;
    this.customPolicy = customPolicy;
    return this;
  }

  public Config withResultWriter(ResultWriter writer) {
    harnessShutdownListeners.add(writer);
    validResultListeners.add(writer);
    invalidResultListeners.add(writer);
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

  public Config withFunctionalTest() {
    functionalTest = true;
    return this;
  }
}
