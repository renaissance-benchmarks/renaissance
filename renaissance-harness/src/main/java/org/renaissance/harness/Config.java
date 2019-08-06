package org.renaissance.harness;

import java.util.*;
import java.util.stream.Collectors;

final class Config {

  enum PolicyType {
    FIXED_OP_COUNT, FIXED_OP_TIME, FIXED_TIME, EXTERNAL;
  }

  final List<String> benchmarkSpecifiers = new ArrayList<>();

  int repetitions = -1;
  int runSeconds = 240;

  final Map<String, List<String>> pluginsWithArgs = new LinkedHashMap<>();

  PolicyType policyType = PolicyType.FIXED_OP_COUNT;
  String externalPolicy;
  List<String> externalPolicyArgs = new ArrayList<>();

  List<String> extraArgs = new ArrayList<>();

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
    this.policyType = PolicyType.FIXED_OP_COUNT;
    this.repetitions = repetitions;
    return this;
  }

  public Config withRunSeconds(int runSeconds) {
    this.policyType = PolicyType.FIXED_TIME;
    this.runSeconds = runSeconds;
    return this;
  }

  public Config withOperationRunSeconds(int runSeconds) {
    this.policyType = PolicyType.FIXED_OP_TIME;
    this.runSeconds = runSeconds;
    return this;
  }

  public Config withPolicy(String policy) {
    this.extraArgs = this.externalPolicyArgs;
    this.policyType = PolicyType.EXTERNAL;
    this.externalPolicy = policy;
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
