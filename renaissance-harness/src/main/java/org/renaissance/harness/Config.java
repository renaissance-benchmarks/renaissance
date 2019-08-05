package org.renaissance.harness;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

final class Config {

  final List<String> benchmarkSpecifiers = new ArrayList<>();

  int repetitions = -1;
  int runSeconds = 240;
  final List<String> plugins = new ArrayList<>();

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
    plugins.add(plugin);
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
