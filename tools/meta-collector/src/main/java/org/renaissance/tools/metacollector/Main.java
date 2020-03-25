package org.renaissance.tools.metacollector;

import java.io.File;
import java.io.IOException;
import java.lang.annotation.Annotation;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Properties;
import java.util.stream.Collectors;

import org.reflections.Reflections;
import org.reflections.scanners.SubTypesScanner;
import org.reflections.scanners.TypeAnnotationsScanner;
import org.reflections.scanners.TypeElementsScanner;
import org.reflections.util.ConfigurationBuilder;

import org.renaissance.Benchmark;
import org.renaissance.License;

public class Main {
    private static class BenchmarkPropertyReader {
        private final Map<String, String> props = new HashMap<>();
        private final Class<?> benchmark;
        private final String name;

        public BenchmarkPropertyReader(Class<?> benchmark) {
            this.benchmark = benchmark;
            this.name = get(Benchmark.Name.class).value();
        }

        public <T extends Annotation> T get(Class<T> annotation) {
            T result = benchmark.getAnnotation(annotation);
            if (result == null) {
                throw new NoSuchElementException("Not present!");
            }
            return result;
        }

        @SuppressWarnings("unchecked")
        public <T extends Annotation> T[] getMany(Class<T> annotation, T[] theType) {
            Annotation all[] = benchmark.getAnnotations();
            List<T> result = new ArrayList<>(all.length);
            for (Annotation a : all) {
                if (a.annotationType().equals(annotation)) {
                    result.add((T)a);
                }
            }
            return result.toArray(theType);
        }

        public void store(String key, String value) {
            props.put(key, value);
        }

        public void makeGlobal(Properties target) {
            for (Map.Entry<String, String> entry : props.entrySet()) {
                String key = String.format("benchmark.%s.%s", name, entry.getKey());
                target.setProperty(key, entry.getValue());
            }
        }
    }

    public static void main(String[] args) throws IOException, ReflectiveOperationException {
        List<URL> classpath = new ArrayList<>();
        List<URL> mainClasses = new ArrayList<>();
        for (String arg : args) {
            URL url = (new File(arg)).toURI().toURL();
            classpath.add(url);
        }
        if (!classpath.isEmpty()) {
            mainClasses.add(classpath.get(0));
        }

        Properties props = new Properties();

        Reflections ref = new Reflections(buildConfiguration(mainClasses, classpath));
        for (Class<?> c : ref.getTypesAnnotatedWith(Benchmark.Name.class)) {
            BenchmarkPropertyReader details = new BenchmarkPropertyReader(c);
            details.store("class", c.getCanonicalName());
            details.store("name", details.get(Benchmark.Name.class).value());
            details.store("group", details.get(Benchmark.Group.class).value());
            details.store("summary", details.get(Benchmark.Summary.class).value());
            try {
                details.store("description", details.get(Benchmark.Description.class).value());
            } catch (NoSuchElementException e) {
                details.store("description", "");
            }
            try {
                details.store("repetitions", Integer.toString(details.get(Benchmark.Repetitions.class).value()));
            } catch (NoSuchElementException e) {
                details.store("repetitions", "20");
            }
            
            License[] licences = details.get(Benchmark.Licenses.class).value();
            details.store("distro", License.getParent(licences).toString());
            String licensesStr = Arrays.stream(licences).map(s -> s.toString()).collect(Collectors.joining(","));
            details.store("licenses", licensesStr);
            
            Map<String, String> defaultParameterValues = new HashMap<>();
            Benchmark.Parameter[] parameters;
            try {
                parameters = details.get(Benchmark.Parameters.class).value();
            } catch (NoSuchElementException e) {
                try {
                    parameters = details.getMany(Benchmark.Parameter.class, new Benchmark.Parameter[0]);
                } catch (NoSuchElementException e2) {
                    parameters = new Benchmark.Parameter[0];
                }
            }
            for (Benchmark.Parameter param : parameters) {
                String prefix = "parameter." + param.name();
                details.store(prefix + ".default", param.defaultValue());
                details.store(prefix + ".summary", param.summary());
                // TODO: announce error on duplication
                defaultParameterValues.put(param.name(), param.defaultValue());
            }
            
            Benchmark.Configuration[] configurations;
            try {
                configurations = details.get(Benchmark.Configurations.class).value();
            } catch (NoSuchElementException e) {
                configurations = new Benchmark.Configuration[0];
            }
            for (Benchmark.Configuration config : configurations) {
                Map<String, String> settings = new HashMap<>();
                settings.putAll(defaultParameterValues);
                for (String initial : config.settings()) {
                    String[] parts = initial.split("=", 2);
                    if (parts.length != 2) {
                        // TODO: announce error
                        continue;
                    }
                    String key = parts[0].trim();
                    String value = parts[1].trim();
                    settings.put(key,  value);
                }
                String prefix = "configuration." + config.name();
                for (String param : defaultParameterValues.keySet()) {
                    details.store(prefix + "." + param, settings.get(param));
                }
            }
            for (Map.Entry<String, String> params : defaultParameterValues.entrySet()) {
                details.store("configuration.default." + params.getKey(), params.getValue());
            }
            
            details.makeGlobal(props);
        }
        
        List<String> propertyNames = getSortedPropertyNames(props);
        
        for (String prop : propertyNames) {
            System.out.printf("%s=%s\n", prop, props.getProperty(prop));
        }
    }

    private static ConfigurationBuilder buildConfiguration(List<URL> mainClasses, List<URL> classpath) {
        URLClassLoader loader = new URLClassLoader(classpath.toArray(new URL[0])); //, Main.class.getClassLoader());
        for (URL u : classpath) {
            //System.err.printf("%s\n", u);
        }
       // URLClassLoader loader = new URLClassLoader(mainClasses.toArray(new URL[0]), Main.class.getClassLoader());
        ConfigurationBuilder config = new ConfigurationBuilder();
        config.addUrls(mainClasses);
        config.addClassLoader(loader);
        //config.addUrls(classpath);
        config.setScanners(new TypeAnnotationsScanner(), new SubTypesScanner());
        //config.setScanners(new TypeElementsScanner(), new SubTypesScanner(), new TypeAnnotationsScanner());
        return config;
    }
    
    private static List<String> getSortedPropertyNames(Properties props) {
        List<String> result = new ArrayList<>();
        result.addAll(props.stringPropertyNames());
        Collections.sort(result);
        return result;
    }

}
