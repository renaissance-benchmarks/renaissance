package org.renaissance.dummy;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.License;

import java.util.List;

import static org.renaissance.Benchmark.*;
import static org.renaissance.BenchmarkResult.Validators.compound;
import static org.renaissance.BenchmarkResult.Validators.simple;

@Name("dummy-param")
@Group("dummy")
@Summary("A dummy benchmark for testing the harness (test configurable parameters).")
@Licenses(License.MIT)
@Parameter(name = "thread_count", defaultValue = "$cpu.count")
@Parameter(name = "meaning_of_life", defaultValue = "42")
@Parameter(name = "beyond_reason", defaultValue = "PI")
@Parameter(name = "reality_check", defaultValue = "3.1415926")
@Parameter(name = "the_sky_is_blue", defaultValue = "true")
@Parameter(name = "tough_choice", defaultValue = "to be, not to be")
@Configuration(name = "test", settings = {"beyond_reason = E", "reality_check = 2.7182818"})
@Configuration(name = "jmh")
public final class DummyParam implements Benchmark {
  @Override
  public BenchmarkResult run(BenchmarkContext c) {
    int threadCountParam = c.parameter("thread_count").toPositiveInteger();
    int meaningOfLifeParam = c.parameter("meaning_of_life").toInteger();
    String beyondReasonParam = c.parameter("beyond_reason").value();
    double realityCheckParam = c.parameter("reality_check").toDouble();
    boolean theSkyIsBlueParam = c.parameter("the_sky_is_blue").toBoolean();
    List<String> toughChoice = c.parameter("tough_choice").toList();

    System.out.printf("thread_count: %d\n", threadCountParam);
    System.out.printf("meaning_of_life: %d\n", meaningOfLifeParam);
    System.out.printf("beyond_reason: %s\n", beyondReasonParam);
    System.out.printf("reality_check: %f\n", realityCheckParam);
    System.out.printf("the_sky_is_blue: %b\n", theSkyIsBlueParam);
    System.out.printf("tough_choice: %s\n", String.join(",", toughChoice));

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
