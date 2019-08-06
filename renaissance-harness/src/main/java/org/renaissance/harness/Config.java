package org.renaissance.harness;

import java.util.*;
import java.util.stream.Collectors;

final class Config {

  final List<String> benchmarkSpecifiers = new ArrayList<>();

  int repetitions = -1;
  int runSeconds = 240;

  final Map<String, List<String>> pluginsWithArgs = new LinkedHashMap<>();
  List<String> extraArgs = new ArrayList<>();

  ExecutionPolicyFactory policyFactory = ExecutionPolicyFactory.FIXED_OP_COUNT;
  String policy = null;

  String csvOutput = null;
  String jsonOutput = null;

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

  public Config withPlugin(String plugin) {
    extraArgs = new ArrayList<>();
    pluginsWithArgs.put(plugin, extraArgs);
    return this;
  }

  public Config withExtraArg(String arg) {
    extraArgs.add(arg);
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

  public Config withPolicy(String policy) {
    this.policyFactory = ExecutionPolicyFactory.CUSTOM;
    this.policy = policy;
    return this;
  }

  public Config withCsvOutput(String outputFile) {
    this.csvOutput = outputFile;
    return this;
  }

  public Config withJsonOutput(String outputFile) {
    this.jsonOutput = outputFile;
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
