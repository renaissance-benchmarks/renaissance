package org.renaissance.util;

public final class BenchmarkInfo {

    final String className;

    final String name;

    final String group;

    final String summary;

    final String description;

    final int repetitions;

    final String[] licenses;

    final String distro;


    BenchmarkInfo(
      String className, String name, String group,
      String summary, String description,
      int repetitions, String[] licenses, String distro
    ) {
      this.className = className;
      this.name = name;
      this.group = group;
      this.summary = summary;
      this.description = description;
      this.repetitions = repetitions;
      this.licenses = licenses;
      this.distro = distro;
    }


    public String name() { return name; }

    public String group() { return group; }

    public String summary() { return summary; }

    public String distro() { return distro; }

    public int repetitions() { return repetitions; }


    public String[] summaryWords() {
      return summary.split("\\s+");
    }


    public String printableLicenses() {
      return String.join(", ", licenses);
    }
}
