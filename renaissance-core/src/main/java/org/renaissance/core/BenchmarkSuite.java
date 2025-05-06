package org.renaissance.core;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkParameter;
import org.renaissance.core.BenchmarkDescriptor.Configuration;
import org.renaissance.core.ModuleLoader.ModuleLoadingException;

import java.io.IOException;
import java.lang.management.ManagementFactory;
import java.lang.management.RuntimeMXBean;
import java.lang.reflect.Constructor;
import java.net.URI;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.function.Predicate;
import java.util.logging.Level;
import java.util.logging.Logger;

import static java.util.function.Function.identity;
import static java.util.stream.Collectors.joining;
import static java.util.stream.Collectors.toCollection;
import static java.util.stream.Collectors.toList;
import static java.util.stream.Collectors.toMap;
import static java.util.stream.Collectors.toSet;
import static org.renaissance.core.ResourceUtils.getManifestAttributeValue;
import static org.renaissance.core.ResourceUtils.getMetadataUrl;
import static org.renaissance.core.ResourceUtils.loadPropertiesAsMap;

/**
 * Provides core services for a benchmark suite. Represents a collection of
 * {@link BenchmarkDescriptor} instances, each of which provides access to
 * benchmark-specific information without having to load or access the
 * benchmark class. In addition to querying and filtering benchmark descriptors,
 * it also provides additional operations on benchmark descriptors that require
 * other runtime elements, as well as services for loading extensions.
 */
public final class BenchmarkSuite {
  private static final Class<?> thisClass = BenchmarkSuite.class;
  private static final Logger logger = Logging.getPackageLogger(thisClass);

  private static final URI moduleMetadataUri = URI.create("resource:/modules.properties");
  private static final URI benchmarkMetadataUri = URI.create("resource:/benchmarks.properties");

  private static final String USE_MODULES_ATTRIBUTE = "Renaissance-Use-Modules";

  private final Path scratchRootDir;
  private final String configurationName;
  private final Optional<ModuleLoader> moduleLoader;


  private final Map<String, BenchmarkDescriptor> benchmarkDescriptors;

  BenchmarkSuite(
    Path scratch, String confName,
    Map<String, BenchmarkDescriptor> descriptors, Optional<ModuleLoader> loader
  ) {
    scratchRootDir = scratch;
    configurationName = confName;
    benchmarkDescriptors = descriptors;
    moduleLoader = loader;
  }

  // Delegation to benchmark registry.

  public boolean hasBenchmark(String benchmarkName) {
    return benchmarkDescriptors.containsKey(benchmarkName);
  }

  public BenchmarkDescriptor getBenchmark(String benchmarkName) {
    final BenchmarkDescriptor result = benchmarkDescriptors.get(benchmarkName);
    if (result != null) {
      return result;
    } else {
      throw new NoSuchElementException("no such benchmark: "+ benchmarkName);
    }
  }

  public boolean hasGroup(String groupName) {
    return groupNames().contains(groupName);
  }

  private Set<String> groupNames() {
    return benchmarkDescriptors.values().stream()
      .flatMap(b -> b.groups().stream())
      .collect(toSet());
  }

  public List<BenchmarkDescriptor> getGroupBenchmarks(String groupName) {
    List<BenchmarkDescriptor> result = getMatchingBenchmarks(b -> b.groups().contains(groupName));
    if (!result.isEmpty()) {
      return result;
    } else {
      throw new NoSuchElementException(String.format(
        "there is no such group: %s", groupName
      ));
    }
  }

  public List<BenchmarkDescriptor> getMatchingBenchmarks(Predicate<BenchmarkDescriptor> matcher) {
    return benchmarkDescriptors.values().stream().filter(matcher).collect(toList());
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
      ClassLoader classLoader = getBenchmarkClassLoader(bd);
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

  private ClassLoader getBenchmarkClassLoader(BenchmarkDescriptor bd) throws ModuleLoadingException {
    //
    // If we have a module loader, create a separate class loader for the
    // benchmark module, otherwise use the classloader of the Benchmark class.
    //
    if (moduleLoader.isPresent()) {
      ModuleLoader loader = this.moduleLoader.get();
      return loader.createClassLoaderForModule(bd.module());
    } else {
      return Benchmark.class.getClassLoader();
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


  public static final class SuiteBenchmarkContext implements BenchmarkContext {
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

  public static final class ExtensionException extends Exception {
    ExtensionException(String message) {
      super(message);
    }

    ExtensionException(String format, Object... args) {
      super(String.format(format, args));
    }
  }

  /** Create classloader from list of Path. */
  private static ClassLoader createClassLoaderFromPaths(
    Collection<Path> classPath,
    String name
  ) throws ExtensionException {
    URL[] classPathUrls = ModuleLoader.pathsToUrls(classPath);
    if (logger.isLoggable(Level.CONFIG)) {
      logger.config(String.format(
        "Class path for %s: %s", name,
        Arrays.stream(classPathUrls).map(Object::toString).collect(joining(","))
      ));
    }

    if (classPathUrls.length != classPath.size()) {
      throw new ExtensionException("malformed URL(s) in classpath specification");
    }

    //
    // No need to explicitly close this URLClassLoader on exit, because it does not
    // operate on files created by the harness that need to be deleted on exit.
    //
    ClassLoader parent = ModuleLoader.class.getClassLoader();
    return new URLClassLoader(classPathUrls, parent);
  }


  /** Loads extension from initialized class loader. */
  static <T> Class<? extends T> loadFromClassLoader(
    ClassLoader loader, String className, Class<T> baseClass
  ) throws ExtensionException {
    try {
      Class<?> loadedClass = loader.loadClass(className);
      return loadedClass.asSubclass(baseClass);

    } catch (ClassNotFoundException e) {
      // Be a bit more verbose, because the ClassNotFoundException
      // on OpenJDK only returns the class name as error message.
      throw new ExtensionException(
        "could not find class '%s'", className
      );
    } catch (ClassCastException e) {
      throw new ExtensionException(
        "class '%s' is not a subclass of '%s'", className, baseClass.getName()
      );
    }
  }


  /** Loads and instantiates an extension class with given arguments. */
  public <T> T createExtension(
    Collection<Path> classPath, String className, Class<T> baseClass, String[] args
  ) throws ExtensionException {
    ClassLoader loader = createClassLoaderFromPaths(classPath, className);
    final Class<? extends T> extClass = loadFromClassLoader(loader, className, baseClass);
    try {
      return ModuleLoader.createExtension(extClass, args);
    } catch (ModuleLoadingException e) {
      throw new ExtensionException(e.getMessage());
    }
  }

  /** Loads and instantiates an extension specified in properties with given arguments. */
  public <T> T createDescribedExtension(
    Collection<Path> classPath, String classNameAttribute, Class<T> baseClass, String[] args
  ) throws ExtensionException {
    ClassLoader loader = createClassLoaderFromPaths(classPath, classNameAttribute);
    Optional<String> className = getManifestAttributeValue(loader, classNameAttribute);
    if (!className.isPresent()) {
      throw new ExtensionException("class name to load not found in manifests");
    }

    final Class<? extends T> extClass = loadFromClassLoader(loader, className.get(), baseClass);

    try {
      return ModuleLoader.createExtension(extClass, args);
    } catch (ModuleLoadingException e) {
      throw new ExtensionException(e.getMessage());
    }
  }

  // Instance creation

  /**
   * Creates a benchmark suite. Loads benchmark descriptors from the given
   * properties file and associates them with parameter overrides.
   */
  public static BenchmarkSuite create(
    Path scratchRoot, String configName,
    Optional<URI> metadataOverrideUri, Map<String, String> parameterOverrides,
    boolean useModules
  ) throws IOException {
    // Use the default benchmark metadata URI unless overridden.
    URI metadataUri = metadataOverrideUri.orElse(benchmarkMetadataUri);
    URL metadataUrl = getMetadataUrl(metadataUri);
    Map<String, String> properties = loadPropertiesAsMap(metadataUrl);
    Map<String, BenchmarkDescriptor> descriptors = createBenchmarkDescriptors(properties, parameterOverrides);

    // The module loader is only created if desired.
    Optional<ModuleLoader> loader = optionallyCreateModuleLoader(scratchRoot, useModules);

    return new BenchmarkSuite(scratchRoot, configName, descriptors, loader);
  }

  private static Optional<ModuleLoader> optionallyCreateModuleLoader(
    Path scratchRoot, boolean useModules
  ) throws IOException {
    if (useModules) {
      return Optional.of(ModuleLoader.create(scratchRoot, moduleMetadataUri));
    } else {
      return Optional.empty();
    }
  }

  private static Map<String, BenchmarkDescriptor> createBenchmarkDescriptors(
    Map<String, String> benchmarkProperties, Map<String, String> parameterOverrides
  ) {
    // Extract benchmark names and a descriptor for each of them.
    return benchmarkNames(benchmarkProperties).stream()
      .map(name -> new BenchmarkDescriptor(name, benchmarkProperties, parameterOverrides))
      .collect(toMap(BenchmarkDescriptor::name, identity()));
  }

  private static SortedSet<String> benchmarkNames(
    Map<String, String> benchmarkProperties
  ) {
    return benchmarkProperties.entrySet().stream()
      .filter(e -> e.getKey().endsWith(".name"))
      .map(e -> e.getValue().trim())
      .collect(toCollection(TreeSet::new));
  }

  /**
   * Queries the value of the {@link #USE_MODULES_ATTRIBUTE} attribute in the
   * manifest accessible from the class loader of this class.
   */
  public static Optional<Boolean> getManifestUseModulesValue() {
    return getManifestAttributeValue(
      thisClass.getClassLoader(), USE_MODULES_ATTRIBUTE
    ).map(Boolean::parseBoolean);
  }

  //

  public static final class BenchmarkSuiteException extends Exception {
    BenchmarkSuiteException(String message) {
      super(message);
    }

    BenchmarkSuiteException(String format, Object... args) {
      super(String.format(format, args));
    }
  }

}
