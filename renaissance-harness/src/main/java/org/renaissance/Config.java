package org.renaissance;

import org.renaissance.harness.Plugin;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

final class Config {
  List<String> benchmarkSpecifiers;
  int repetitions;
  int runSeconds;
  List<Plugin> plugins;
  String policy;

  List<Plugin.HarnessInitListener> harnessInitListeners;
  List<Plugin.HarnessShutdownListener> harnessShutdownListeners;
  List<Plugin.BenchmarkSetUpListener> benchmarkSetUpListeners;
  List<Plugin.BenchmarkTearDownListener> benchmarkTearDownListeners;
  List<Plugin.ValidResultListener> validResultListeners;
  List<Plugin.InvalidResultListener> invalidResultListeners;

  boolean printList;
  boolean printRawList;
  boolean printGroupList;
  boolean functionalTest;


  public Config() {
    this.benchmarkSpecifiers = new ArrayList<>();
    this.repetitions = -1;
    this.runSeconds = 240;
    this.plugins = new ArrayList<>();
    this.policy = "fixed-count"; // !@$# Policy.kebabCasePolicy(FixedIterationsPolicy.class);

    this.harnessInitListeners = new ArrayList<>();
    this.harnessShutdownListeners = new ArrayList<>();
    this.benchmarkSetUpListeners = new ArrayList<>();
    this.benchmarkTearDownListeners = new ArrayList<>();
    this.validResultListeners = new ArrayList<>();
    this.invalidResultListeners = new ArrayList<>();

    this.printList = false;
    this.printRawList = false;
    this.printGroupList = false;
    this.functionalTest = false;
  }

  public List<String> benchmarkSpecifiers() {
    return benchmarkSpecifiers;
  }

  public int repetitions() {
    return repetitions;
  }

  public List<Plugin> plugins() {
    return plugins;
  }

  // TODO Rename to executionPolicy
  public String policy() {
    return policy;
  }

  public boolean printList() {
    return printList;
  }

  public boolean printRawList() {
    return printRawList;
  }

  public boolean functionalTest() {
    return functionalTest;
  }

  public Config copy() {
    Config c = new Config();
    c.benchmarkSpecifiers = this.benchmarkSpecifiers;
    c.repetitions = this.repetitions;
    c.runSeconds = this.runSeconds;
    c.plugins = this.plugins;
    c.policy = this.policy;

    c.harnessInitListeners = new ArrayList<>(this.harnessInitListeners);
    c.harnessShutdownListeners = new ArrayList<>(this.harnessShutdownListeners);
    c.benchmarkSetUpListeners = new ArrayList<>(this.benchmarkSetUpListeners);
    c.benchmarkTearDownListeners = new ArrayList<>(this.benchmarkTearDownListeners);
    c.validResultListeners = new ArrayList<>(this.validResultListeners);
    c.invalidResultListeners = new ArrayList<>(this.invalidResultListeners);

    c.printList = this.printList;
    c.printRawList = this.printRawList;
    c.printGroupList = this.printGroupList;
    c.functionalTest = this.functionalTest;
    return c;
  }

  public Config withBenchmarkSpecification(String v) {
    Config c = copy();
    c.benchmarkSpecifiers = Arrays.stream(v.split(",")).collect(Collectors.toList());
    return c;
  }

  public Config withPlugins(String v) {
    Config c = copy();
    c.plugins = Arrays.stream(v.split(","))
      .map(n -> {
        try {
          return (Plugin) Class.forName(v).newInstance();
        } catch (Throwable e) {
          throw new RuntimeException(e);
        }
      })
      .collect(Collectors.toList());
    return c;
  }

  public Config withRepetitions(int x) {
    Config c = copy();
    c.repetitions = x;
    return c;
  }

  public Config withRunSeconds(int seconds) {
    Config c = copy();
    c.runSeconds = seconds;
    return c;
  }

  public Config withPolicy(String policy) {
    Config c = copy();
    c.policy = policy;
    return c;
  }

  public Config withResultWriter(ResultWriter writer) {
    Config c = copy();
    c.harnessShutdownListeners.add(writer);
    c.validResultListeners.add(writer);
    c.invalidResultListeners.add(writer);
    return c;
  }

  public Config withList() {
    Config c = copy();
    c.printList = true;
    return c;
  }

  public Config withRawList() {
    Config c = copy();
    c.printRawList = true;
    return c;
  }

  public Config withGroupList() {
    Config c = copy();
    c.printGroupList = true;
    return c;
  }

  public Config withFunctionalTest() {
    Config c = copy();
    c.functionalTest = true;
    return c;
  }
}
