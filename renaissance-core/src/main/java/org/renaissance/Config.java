package org.renaissance;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class Config {
  public List<String> benchmarkSpecifiers;
  public int repetitions;
  public int warmupSeconds;
  public int runSeconds;
  public List<Plugin> plugins;
  public String policy;
  public List<ResultObserver> resultObservers;
  public boolean readme;
  public boolean printList;
  public boolean printRawList;
  public boolean printGroupList;
  public boolean functionalTest;

  public Config() {
    this.benchmarkSpecifiers = new ArrayList<>();
    this.repetitions = -1;
    this.warmupSeconds = 180;
    this.runSeconds = 60;
    this.plugins = new ArrayList<>();
    this.policy = Policy.kebabCasePolicy(FixedIterationsPolicy.class);
    this.resultObservers = new ArrayList<>();
    this.readme = false;
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

  public String policy() {
    return policy;
  }

  public List<ResultObserver> resultObservers() {
    return resultObservers;
  }

  public boolean readme() {
    return readme;
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
    c.warmupSeconds = this.warmupSeconds;
    c.runSeconds = this.runSeconds;
    c.plugins = this.plugins;
    c.policy = this.policy;
    c.resultObservers = new ArrayList<>(this.resultObservers);
    c.readme = this.readme;
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

  public Config withWarmupSeconds(int seconds) {
    Config c = copy();
    c.warmupSeconds = seconds;
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

  public Config withResultObserver(ResultObserver observer) {
    Config c = copy();
    c.resultObservers.add(observer);
    return c;
  }

  public Config withReadme(boolean readme) {
    Config c = copy();
    c.readme = readme;
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
