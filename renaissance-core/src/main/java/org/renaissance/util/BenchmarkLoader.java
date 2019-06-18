package org.renaissance.util;

import org.renaissance.RenaissanceBenchmark;

import java.io.IOException;
import java.util.Properties;
import java.util.TreeMap;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

public class BenchmarkLoader {
    private final Properties properties;
    private final TreeMap<String, Info> benchmarksByName;

    public BenchmarkLoader() {
        try {
            this.properties = new Properties();
            this.properties.load(getClass().getResourceAsStream("/benchmark-details.properties"));
            this.benchmarksByName = properties.stringPropertyNames().stream()
                    .filter(p -> p.endsWith(".name"))
                    .collect(Collectors.toMap(
                            p -> properties.getProperty(p),
                            p -> info(properties.getProperty(p)),
                            (x, y) -> y,
                            () -> new TreeMap<>()
                    ));
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    public TreeMap<String, Info> loadBenchmarkInfoByName() {
        return benchmarksByName;
    }

    public RenaissanceBenchmark loadBenchmark(String name) {
        try {
            final Info bench = benchmarksByName.get(name);
            final ClassLoader loader = ModuleLoader.getForGroup(bench.group);
            final Class<?> benchClass = loader.loadClass(bench.className);
            final Object result = benchClass.getDeclaredConstructor().newInstance();

            // Make current thread as independent of the harness as possible.
            Thread.currentThread().setContextClassLoader(loader);
            return (RenaissanceBenchmark) result;
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }

    private Info info(String name) {
        BiFunction<String, String, String> getter = (key, defaultValue) -> {
            return properties.getProperty("benchmark." + name + "." + key, defaultValue);
        };
        return new Info(
                getter.apply("class", ""),
                getter.apply("name", ""),
                getter.apply("group", ""),
                getter.apply("summary", ""),
                getter.apply("description", ""),
                Integer.valueOf(getter.apply("repetitions", "20")),
                getter.apply("licenses", "").split(","),
                getter.apply("distro", "")
        );
    }

    public static final class Info {
        public final String className;
        public final String name;
        public final String group;
        public final String summary;
        public final String description;
        public final int repetitions;
        public final String[] licenses;
        public final String distro;

        public Info(
                String className,
                String name,
                String group,
                String summary,
                String description,
                int repetitions,
                String[] licenses,
                String distro
        ) {
            this.className = className;
            this.name = name;
            this.group = group;
            this.summary = summary;
            this.description = description;
            this.repetitions = repetitions;
            this.licenses = licenses;
            this.distro = distro;
        }

        public String[] summaryWords() {
            return summary.split("\\s+");
        }

        public String printableLicenses() {
            return String.join(", ", licenses);
        }
    }
}
