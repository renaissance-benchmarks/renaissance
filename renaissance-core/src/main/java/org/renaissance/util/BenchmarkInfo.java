package org.renaissance.util;

public final class BenchmarkInfo {

    public final String className;

    public final String name;

    public final String group;

    public final String summary;

    public final String description;

    public final int repetitions;

    public final String[] licenses;

    public final String distro;


    BenchmarkInfo(
      String className, String name, String group, String summary, String description,
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


    public String[] summaryWords() {
      return summary.split("\\s+");
    }


    public String printableLicenses() {
      return String.join(", ", licenses);
    }

  }
