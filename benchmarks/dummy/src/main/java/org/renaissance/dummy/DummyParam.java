package org.renaissance.dummy;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.License;

import static org.renaissance.Benchmark.*;
import static org.renaissance.BenchmarkResult.compound;
import static org.renaissance.BenchmarkResult.simple;

@Name("dummy-param")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (test configurable parameters).")
@Licenses(License.MIT)
@Parameter(name = "thread_count", defaultValue = "$cpu.count")
@Parameter(name = "meaning_of_life", defaultValue = "42")
@Parameter(name = "beyond_reason", defaultValue = "PI")
@Parameter(name = "reality_check", defaultValue = "3.1415926")
@Configuration(name = "test", settings = {"beyond_reason = E", "reality_check = 2.7182818"})
@Configuration(name = "jmh")
public final class DummyParam implements Benchmark {
  @Override
  public BenchmarkResult runIteration(BenchmarkContext c) {
    int threadCountParam = c.intParameter("thread_count");
    int meaningOfLifeParam = c.intParameter("meaning_of_life");
    String beyondReasonParam = c.stringParameter("beyond_reason");
    double realityCheckParam = c.doubleParameter("reality_check");

    System.out.printf("thread_count: %d\n", threadCountParam);
    System.out.printf("meaning_of_life: %d\n", meaningOfLifeParam);
    System.out.printf("beyond_reason: %s\n", beyondReasonParam);
    System.out.printf("reality_check: %f\n", realityCheckParam);

    try {
      double beyondReasonValue = Math.class.getField(beyondReasonParam).getDouble(null);

      return compound(
        simple("computed int parameter", Runtime.getRuntime().availableProcessors(), threadCountParam),
        simple("constant int parameter", 42, meaningOfLifeParam),
        simple("constant double parameter", realityCheckParam, beyondReasonValue, 0.000001)
      );
    } catch (ReflectiveOperationException e) {
      throw new RuntimeException(e);
    }
  }
}
