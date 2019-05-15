package org.renaissance;

public enum License {
  APACHE2("Apache Public License 2.0"),
  MIT("MIT License"),
  BSD3("BSD 3-Clause License"),
  PUBLIC("Public Domain"),
  MPL2("Mozilla Public License 2"),
  EPL1("Eclipse Public License 1"),
  GPL2("GNU Public License 2"),
  GPL3("GNU Public License 3");

  private final String name;

  License(String name) {
    this.name = name;
  }

  public String getName() {
    return name;
  }

  public static License[] create(License... licenses) {
    return licenses;
  }

}
