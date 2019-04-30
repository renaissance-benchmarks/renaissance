package org.renaissance;

import java.util.Optional;

public interface RenaissanceBenchmarkApi {
  String name();

  String mainGroup();

  String description();

  License[] licenses();

  License distro();

  int defaultRepetitions();

  Optional<String> initialRelease();

  Optional<String> finalRelease();

  void setUpBeforeAll(Config c);

  void tearDownAfterAll(Config c);

  void beforeIteration(Config c);

  void afterIteration(Config c);

  Throwable runBenchmark(Config config);
}
