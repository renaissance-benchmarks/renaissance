package org.renaissance;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.Set;

public class HashingResult implements BenchmarkResult {
  private final String expected;
  private final Collection<?> values;
  private final boolean needsSorting;

  public HashingResult(String hash, Set<?> values) {
    assert hash != null;
    assert values != null;

    this.expected = hash;
    this.values = values;
    needsSorting = true;
  }

  public HashingResult(String hash, List<?> values) {
    assert hash != null;
    assert values != null;

    this.expected = hash;
    this.values = values;
    needsSorting = false;
  }

  @Override
  public void validate() {
    List<String> vals = getSortedValues();
    long hash = 0;
    for (String v : vals) {
      hash = 31 * hash + getStringHash(v);
    }

    String actual = String.format("%16x", hash);
    
    ValidationException.throwIfNotEqual(expected, actual, "object hash");
  }

  private List<String> getSortedValues() {
    ArrayList<String> sorted = new ArrayList<>(values.size());
    for (Object val : values) {
      if (val == null) {
        sorted.add("null");
      } else {
        sorted.add(val.toString());
      }
    }

    if (needsSorting) {
      Collections.sort(sorted);
    }

    return sorted;
  }

  private long getStringHash(final String value) {
    long result = 0;
    for (char c : value.toCharArray()) {
      result = result * 31 + c;
    }
    return result;
  }

}
