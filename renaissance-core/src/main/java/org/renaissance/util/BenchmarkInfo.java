package org.renaissance.util;

import java.util.Map;

public final class BenchmarkInfo {

    final String className;

    final String name;

    final String group;

    final String summary;

    final String description;

    final int repetitions;

    final String[] licenses;

    final String distro;

    final Map<String, Map<String, String>> configurations;


    BenchmarkInfo(
      String className, String name, String group,
      String summary, String description,
      int repetitions, String[] licenses, String distro,
      Map<String, Map<String, String>> configurations
    ) {
      this.className = className;
      this.name = name;
      this.group = group;
      this.summary = summary;
      this.description = description;
      this.repetitions = repetitions;
      this.licenses = licenses;
      this.distro = distro;
      this.configurations = configurations;
    }


    public String name() { return name; }

    public String group() { return group; }

    public String summary() { return summary; }

    public String distro() { return distro; }

    public int repetitions() { return repetitions; }


    public String[] configurationNames() {
      return configurations.keySet().toArray(new String[0]);
    }


    public String[] parameterNames(String confName) {
      if (configurations.containsKey(confName)) {
        return configurations.get(confName).keySet().toArray(new String[0]);
      } else {
        return null;
      }
    }

    public String parameter(String confName, String paramName) {
      if (configurations.containsKey(confName)) {
        return configurations.get(confName).get(paramName);
      } else {
        return null;
      }
    }

    public String[] summaryWords() {
      return summary.split("\\s+");
    }


    public String printableLicenses() {
      return String.join(", ", licenses);
    }
}
