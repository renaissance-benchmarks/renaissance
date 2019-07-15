package org.renaissance;

import java.io.IOException;
import java.io.InputStream;
import java.util.Properties;

public class BenchmarkParameters {
  private static final String PROPS_FILENAME = "/benchmark-details.properties";
  private static final Properties PROPS = loadDetailsProperties();

  public static int get(String benchmark, String configuration, String parameter) {
    if (PROPS == null) {
      throw new IllegalArgumentException(String.format(
        "Unable to load in-JAR properties %s", PROPS_FILENAME));
    }

    String propName = String.format("benchmark.%s.parameters.%s.%s",
      benchmark, configuration, parameter);
    String value = PROPS.getProperty(propName);
    if (value == null) {
      throw new IllegalArgumentException(String.format(
        "Configuration option %s not found", propName));
    }

    if (value.equals("cpu.count")) {
      return Runtime.getRuntime().availableProcessors();
    }
    try {
      return Integer.parseInt(value);
    } catch (NumberFormatException e) {
      throw new IllegalArgumentException(String.format(
        "Configuration option %s is not integer (%s)", propName, value));
    }
  }

  private static Properties loadDetailsProperties() {
    Properties properties = new Properties();
    InputStream input = BenchmarkParameters.class.getResourceAsStream(PROPS_FILENAME);
    try {
      properties.load(input);
    } catch (IOException e) {
      return null;
    }
    return properties;
  }
}
