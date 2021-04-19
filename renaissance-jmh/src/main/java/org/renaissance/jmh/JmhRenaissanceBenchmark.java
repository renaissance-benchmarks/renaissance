package org.renaissance.jmh;

import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Level;
import org.openjdk.jmh.annotations.Measurement;
import org.openjdk.jmh.annotations.Mode;
import org.openjdk.jmh.annotations.OutputTimeUnit;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.TearDown;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.ValidationException;
import org.renaissance.core.BenchmarkInfo;
import org.renaissance.core.BenchmarkRegistry;
import org.renaissance.core.DirUtils;
import org.renaissance.core.ModuleLoader;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import static java.util.concurrent.TimeUnit.MILLISECONDS;

public abstract class JmhRenaissanceBenchmark {
  private final Path scratchRootDir;
  private final org.renaissance.Benchmark benchmark;
  private final BenchmarkContext context;

  private BenchmarkResult result;
  private Path scratchDir;

  protected JmhRenaissanceBenchmark(final String name) {
    try {
      scratchRootDir = DirUtils.createScratchDirectory(
        Paths.get(""), "jmh-", false
      );

    } catch (IOException e) {
      throw new RuntimeException("failed to create scratch root", e);
    }

    final ModuleLoader moduleLoader = ModuleLoader.create(scratchRootDir);
    BenchmarkInfo benchInfo = BenchmarkRegistry.createDefault().get(name);
    benchmark = benchInfo.loadBenchmarkModule(moduleLoader);
    context = createBenchmarkContext(benchInfo);
  }

  @Setup(Level.Trial)
  public final void setUpBenchmark() {
    benchmark.setUpBeforeAll(context);
  }

  @Setup(Level.Iteration)
  public final void setUpOperation() {
    benchmark.setUpBeforeEach(context);
  }

  @Benchmark
  @BenchmarkMode(Mode.SingleShotTime)
  @OutputTimeUnit(MILLISECONDS)
  @Measurement(timeUnit = MILLISECONDS)
  public final void runOperation() {
    result = benchmark.run(context);
  }

  @TearDown(Level.Iteration)
  public final void tearDownOperation() throws ValidationException {
    benchmark.tearDownAfterEach(context);

    result.validate();
    result = null;
  }

  @TearDown(Level.Trial)
  public final void defaultTearBenchmark() {
    benchmark.tearDownAfterAll(context);
  }

  //

  private BenchmarkContext createBenchmarkContext(BenchmarkInfo benchInfo) {
    return new BenchmarkContext() {

      @Override
      public int intParameter(String name) {
        return Integer.parseInt(stringParameter(name));
      }

      @Override
      public double doubleParameter(String name) {
        return Double.parseDouble(stringParameter(name));
      }

      @Override
      public String stringParameter(String name) {
        return benchInfo.parameter("jmh", name);
      }

      @Override
      public Path scratchDirectory() {
        if (scratchDir == null) {
          try {
            scratchDir = Files.createDirectories(
              scratchRootDir.resolve(benchInfo.name()).resolve("scratch")
            ).normalize();
          } catch (IOException e) {
            // This is a problem, fail the benchmark.
            throw new RuntimeException("failed to create benchmark scratch directory", e);
          }
        }

        return scratchDir;
      }
    };
  }

}
