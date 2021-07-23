package org.renaissance.core;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkParameter;
import org.renaissance.core.BenchmarkDescriptor.Configuration;
import org.renaissance.core.ModuleLoader.ModuleLoadingException;

import java.io.InputStream;
import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.RuntimeMXBean;
import java.lang.reflect.Constructor;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collection;
import java.util.Enumeration;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.function.Predicate;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

/**
 * Provides core services for a benchmark suite. In addition to querying
 * and filtering benchmark descriptors, these also include additional services
 * on benchmark descriptors that require other runtime elements, as well as
 * services for loading extensions.
 */
public final class BenchmarkSuite {
  private static final Class<?> thisClass = BenchmarkSuite.class;
  private static final Logger logger = Logging.getPackageLogger(thisClass);

  private final Path scratchRootDir;
  private final String configurationName;
  private final ModuleLoader moduleLoader;
  private final BenchmarkRegistry benchmarkRegistry;

  BenchmarkSuite(
    Path scratch, String confName,
    ModuleLoader loader, BenchmarkRegistry registry
  ) {
    scratchRootDir = scratch;
    configurationName = confName;
    moduleLoader = loader;
    benchmarkRegistry = registry;
  }

  // Delegation to benchmark registry.

  public boolean hasBenchmark(String benchmarkName) {
    return benchmarkRegistry.hasBenchmark(benchmarkName);
  }

  public BenchmarkDescriptor getBenchmark(String benchmarkName) {
    return benchmarkRegistry.getBenchmark(benchmarkName);
  }

  public boolean hasGroup(String groupName) {
    return benchmarkRegistry.hasGroup(groupName);
  }

  public List<BenchmarkDescriptor> getGroupBenchmarks(String groupName) {
    return benchmarkRegistry.getGroupBenchmarks(groupName);
  }

  public List<BenchmarkDescriptor> getMatchingBenchmarks(Predicate<BenchmarkDescriptor> matcher) {
    return benchmarkRegistry.getMatchingBenchmarks(matcher);
  }

  // Other convenience methods

  /** Returns the specification version of this JVM. */
  public static Version jvmSpecVersion() {
    final RuntimeMXBean runtimeMXBean = ManagementFactory.getRuntimeMXBean();
    return Version.parse(runtimeMXBean.getSpecVersion());
  }

  // Extra services for benchmark descriptors

  /**
   * Determines the given benchmark is compatible with this JVM.
   */
  public boolean isBenchmarkCompatible(BenchmarkDescriptor bd) {
    final Version jvmVersion = jvmSpecVersion();
    boolean minSatisfied = jvmVersion.compareTo(bd.jvmVersionMin()) >= 0;
    boolean maxSatisfied = jvmVersion.compareTo(bd.jvmVersionMax()) <= 0;
    return minSatisfied && maxSatisfied;
  }


  /**
   * Creates a {@link Benchmark} instance for the given {@link BenchmarkDescriptor}.
   */
  public Benchmark createBenchmark(BenchmarkDescriptor bd) {
    try {
      ClassLoader classLoader = moduleLoader.createClassLoaderForModule(bd.module());
      Class<?> loadedClass = classLoader.loadClass(bd.className());
      Class<? extends Benchmark> benchClass = loadedClass.asSubclass(Benchmark.class);
      Constructor<? extends Benchmark> benchCtor = benchClass.getDeclaredConstructor();

      // Make the current thread as independent of the harness as possible.
      Thread.currentThread().setContextClassLoader(classLoader);
      return benchCtor.newInstance();

    } catch (Exception e) {
      throw new RuntimeException("failed to load benchmark "+ bd.name(), e);
    }
  }


  /**
   * Creates a {@link BenchmarkContext} implementation for the given
   * {@link BenchmarkDescriptor} and configuration name. This also involves
   * creating the benchmark's scratch directory. The method actually returns
   * a {@link SuiteBenchmarkContext} instance for use by the harness.
   */
  public SuiteBenchmarkContext createBenchmarkContext(BenchmarkDescriptor bd) {
    final Path scratchDir = createScratchDir(bd);
    final Configuration configuration = bd.getConfiguration(configurationName);

    if (configuration.hasOverrides()) {
      printParameterOverrides(configuration);
    }

    return new SuiteBenchmarkContext(scratchDir, configuration);
  }


  /**
   * Creates a scratch directory for the given benchmark. The scratch
   * directory is resolved against the suite scratch root directory.
   */
  private Path createScratchDir(BenchmarkDescriptor bd) {
    try {
      return Files.createDirectories(
        // Resolve placement with respect to the suite scratch root.
        scratchRootDir.resolve(bd.module()).resolve(bd.name())
      ).normalize();
    } catch (IOException e) {
      // This is a problem, fail the benchmark.
      throw new RuntimeException("failed to create benchmark scratch directory", e);
    }
  }


  private void printParameterOverrides(Configuration configuration) {
    System.out.printf(
      "Overriding '%s' benchmark configuration parameters:\n",
      configuration.benchmarkName()
    );

    configuration.overriddenParameters().forEach(
      p -> System.out.printf(
        // We only process overrides, so calling get() is safe here.
        "* %s: %s -> %s\n", p.name(), p.baseValue(), p.overrideValue().get()
      )
    );
  }


  public final class SuiteBenchmarkContext implements BenchmarkContext {
    private final Path scratchDir;
    private final Configuration configuration;

    SuiteBenchmarkContext(
      Path scratchDir, Configuration configuration
    ) {
      this.scratchDir = scratchDir;
      this.configuration = configuration;
    }

    public String benchmarkName() {
      return configuration.benchmarkName();
    }

    public String benchmarkPrimaryGroup() {
      return configuration.benchmarkPrimaryGroup();
    }

    /**
     * Returns the visible configuration name for a given benchmark.
     */
    public String configurationName() {
      return configuration.name();
    }

    // Normal BenchmarkContext

    @Override
    public BenchmarkParameter parameter(String name) {
      return configuration.getParameter(name);
    }

    @Override
    public Path scratchDirectory() {
      return scratchDir;
    }
  }

  // Extension support

/** Read all manifests and find first one having given property.
   * @returns Property value or null if not found.
   */
  private static String getManifestProperty(ClassLoader loader, String property) {
    try {
      Enumeration<URL> manifests = loader.getResources("META-INF/MANIFEST.MF");
      while (manifests.hasMoreElements()) {
        try {
          URL manifestUrl = manifests.nextElement();
          Properties props = new Properties();
          InputStream manifest = manifestUrl.openStream();
          props.load(manifest);
          manifest.close();
          if (props.containsKey(property)) {
            return props.getProperty(property);
          }
        } catch (IOException e) {
          continue;
        }
      }
    } catch (IOException e) {
      // Ignore.
    }
    return null;
  }

 /** Create classloader from list of Path. */
  private static ClassLoader createClassLoaderFromPaths(
    Collection<Path> classPath,
    String name
  ) throws ModuleLoadingException {
    URL[] classPathUrls = ModuleLoader.pathsToUrls(classPath);
    if (logger.isLoggable(Level.CONFIG)) {
      logger.config(String.format(
        "Class path for %s: %s", name,
        Arrays.stream(classPathUrls).map(Object::toString).collect(Collectors.joining(","))
      ));
    }

    if (classPathUrls.length != classPath.size()) {
      throw new ModuleLoadingException("malformed URL(s) in classpath specification");
    }

    ClassLoader parent = ModuleLoader.class.getClassLoader();
    return new URLClassLoader(classPathUrls, parent);
  }


  /** Loads extension from initialized class loader. */
  static <T> Class<? extends T> loadFromClassLoader(
    ClassLoader loader, String className, Class<T> baseClass
  ) throws ModuleLoadingException {
    try {
      Class<?> loadedClass = loader.loadClass(className);
      return loadedClass.asSubclass(baseClass);

    } catch (ClassNotFoundException e) {
      // Be a bit more verbose, because the ClassNotFoundException
      // on OpenJDK only returns the class name as error message.
      throw new ModuleLoadingException(
        "could not find class '%s'", className
      );
    } catch (ClassCastException e) {
      throw new ModuleLoadingException(
        "class '%s' is not a subclass of '%s'", className, baseClass.getName()
      );
    }
  }


  /** Loads and instantiates an extension class with given arguments. */
  public <T> T createExtension(
    List<Path> classPath, String className, Class<T> baseClass, String[] args
  ) throws ModuleLoadingException {
    ClassLoader loader = createClassLoaderFromPaths(classPath, className);
    final Class<? extends T> extClass = loadFromClassLoader(loader, className, baseClass);
    return ModuleLoader.createExtension(extClass, args);
  }

  /** Loads and instantiates an extension specified in properties with given arguments. */
  public <T> T createDescribedExtension(
    List<Path> classPath, String propertyName, Class<T> baseClass, String[] args
  ) throws ModuleLoadingException {
    ClassLoader loader = createClassLoaderFromPaths(classPath, propertyName);
    String className = getManifestProperty(loader, propertyName);

    if (className == null) {
      throw new ModuleLoadingException("classname to load not found in manifests");
    }

    final Class<? extends T> extClass = loadFromClassLoader(loader, className, baseClass);
    return ModuleLoader.createExtension(extClass, args);
  }


  // Instance creation

  /** Creates a benchmark suite core without parameter overrides. */
  public static BenchmarkSuite create(Path scratchRoot, String configName) {
    final ModuleLoader loader = ModuleLoader.create(scratchRoot);
    final BenchmarkRegistry registry = BenchmarkRegistry.create();
    return new BenchmarkSuite(scratchRoot, configName, loader, registry);
  }


  /** Creates a benchmark suite core with parameter overrides. */
  public static BenchmarkSuite create(
    Path scratchRoot, String configName, Map<String, String> parameterOverrides
  ) {
    final ModuleLoader loader = ModuleLoader.create(scratchRoot);
    final BenchmarkRegistry registry = BenchmarkRegistry.create(parameterOverrides);
    return new BenchmarkSuite(scratchRoot, configName, loader, registry);
  }

}
