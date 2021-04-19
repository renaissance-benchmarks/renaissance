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
import org.renaissance.core.Version;

import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.RuntimeMXBean;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Optional;

import static java.util.concurrent.TimeUnit.MILLISECONDS;

public abstract class JmhRenaissanceBenchmark {

  /**
   * Determines whether to fake runs for incompatible benchmarks. This
   * is needed to avoid JMH failures in automated runs using different JVM
   * versions. Some of the benchmarks require specific range of JVM versions
   * and there is no way to signal incompatibility from JMH, apart from an
   * exception (which will fail JMH).
   */
  private static final boolean fakeIncompatibleBenchmarks = Boolean.parseBoolean(
    System.getProperty("org.renaissance.jmh.fakeIncompatible", "false")
  );

  /** Base directory in which to create scratch directories. */
  private static final String scratchBaseDir = System.getProperty(
    "org.renaissance.jmh.scratchBase", ""
  );

  /** Determines whether to avoid removing scratch directories on VM exit. */
  private static final boolean keepScratch = Boolean.parseBoolean(
    System.getProperty("org.renaissance.jmh.keepScratch", "false")
  );

  private final Path scratchRootDir;
  private final org.renaissance.Benchmark benchmark;
  private final BenchmarkContext context;

  private BenchmarkResult result;
  private Path scratchDir;

  protected JmhRenaissanceBenchmark(final String name) {
    // Get benchmark information and fake the run if necessary.
    final BenchmarkRegistry benchmarks = BenchmarkRegistry.createDefault();
    BenchmarkInfo benchInfo = benchmarks.get(name);
    if (!benchmarkIsCompatible(benchInfo)) {
      String message = String.format(
        "Benchmark '%s' is not compatible with this JVM version!", benchInfo.name()
      );

      if (!fakeIncompatibleBenchmarks) {
        throw new RuntimeException(message);
      } else {
        benchInfo = benchmarks.get("dummy-empty");
      }

      System.out.printf(
        "\n!!!!! %s. Using '%s' instead to avoid failure. !!!!!\n",
        message, benchInfo.name()
      );
    }

    // Create scratch root so that we can initialize module loader.
    try {
      scratchRootDir = DirUtils.createScratchDirectory(
        Paths.get(scratchBaseDir), "jmh-", keepScratch
      );

    } catch (IOException e) {
      throw new RuntimeException("failed to create scratch root", e);
    }

    // Load the benchmark.
    final ModuleLoader moduleLoader = ModuleLoader.create(scratchRootDir);
    benchmark = benchInfo.loadBenchmarkModule(moduleLoader);
    context = createBenchmarkContext(benchInfo);
  }

  private static boolean benchmarkIsCompatible(BenchmarkInfo b) {
    RuntimeMXBean runtimeMXBean = ManagementFactory.getRuntimeMXBean();
    Version jvmVersion = Version.parse(runtimeMXBean.getSpecVersion());

    boolean minSatisfied = compare(jvmVersion, b.jvmVersionMin()) >= 0;
    boolean maxSatisfied = compare(jvmVersion, b.jvmVersionMax()) <= 0;

    return minSatisfied && maxSatisfied;
  }

  private static int compare(Version v1, Optional<Version> maybeV2) {
    return maybeV2.map(v2 -> v1.compareTo(v2)).orElse(0);
  }

  //

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
