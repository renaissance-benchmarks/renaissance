package org.renaissance.json;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.ObjectReader;
import com.fasterxml.jackson.databind.ObjectWriter;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;

import org.renaissance.Benchmark;
import org.renaissance.BenchmarkContext;
import org.renaissance.BenchmarkResult;
import org.renaissance.BenchmarkResult.Validators;
import org.renaissance.License;

import static org.renaissance.Benchmark.*;

import java.io.IOException;
import java.util.ArrayList;
import java.util.concurrent.Callable;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

@Name("json-dom")
@Group("json")
@Summary("Runs workload based on serialization of Java objects to JSON strings and back using the Jackson library.")
@Licenses(License.MIT)
@Repetitions(20)
@Parameter(name = "threads", defaultValue = "1", summary = "Number of threads to process the workload")
@Parameter(name = "seed", defaultValue = "42", summary = "Seed used for the basic java.util.Random generator")
@Parameter(name = "count", defaultValue = "1000", summary = "Number of root objects to be serialized and deserialized")
@Parameter(name = "branching", defaultValue = "4", summary = "Branching factor of the object tree")
@Parameter(name = "depth", defaultValue = "2", summary = "Branching factor of the object tree")
@Configuration(name = "5-large", settings = { "threads = 1", "count = 5", "branching = 5", "depth = 6" })
@Configuration(name = "1k-medium", settings = { "threads = 2", "count = 1000", "branching = 4", "depth = 2" })
@Configuration(name = "100k-small", settings = { "threads = 4", "count = 100000", "branching = 0", "depth = 0" })
public final class JsonDomProcessing implements Benchmark {
	private int threads;
	private int seed;
	private int count;
	private int branching;
	private int depth;

	private ObjectMapper objectMapper;
	private ObjectWriter writer;
	private ObjectReader reader;

	private Employee rootEmployee;
	private ArrayList<Callable<Object>> tasks;
	private ExecutorService execService;

	private final Callable<Object> task = () -> {
		byte[] serialized = writer.writeValueAsBytes(rootEmployee);
		Employee deserializedEmployee = reader.readValue(serialized, Employee.class);
		return null;
	};

	@Override
	public void setUpBeforeAll(BenchmarkContext context) {
		threads = context.parameter("threads").toPositiveInteger();
		seed = context.parameter("seed").toPositiveInteger();
		count = context.parameter("count").toPositiveInteger();
		branching = context.parameter("branching").toPositiveInteger();
		depth = context.parameter("depth").toPositiveInteger();

		objectMapper = new ObjectMapper();
		objectMapper.registerModule(new JavaTimeModule());
		writer = objectMapper.writer();
		reader = objectMapper.reader();

		final EmployeeGenerator employeeGen = new EmployeeGenerator(seed);
		rootEmployee = employeeGen.createEmployee(branching, depth);

		if (threads > 1) {
			execService = Executors.newWorkStealingPool(threads);
			tasks = new ArrayList<>();

			for (int i = 0; i < count - 1; i++) {
				tasks.add(task);
			}
		}
	}

	@Override
	public void tearDownAfterAll(BenchmarkContext context) {
		if (execService != null) {
			execService.shutdown();

			try {
				execService.awaitTermination(1, TimeUnit.SECONDS);
			} catch (final InterruptedException e) {
				throw new RuntimeException(e);
			}
		}
	}

	@Override
	public BenchmarkResult run(BenchmarkContext context) {
		try {
			if (threads < 2) {
				for (int i = 0; i < count - 1; i++) {
					byte[] serialized = writer.writeValueAsBytes(rootEmployee);
					Employee deserializedEmployee = reader.readValue(serialized, Employee.class);
				}
			} else {
				try {
					execService.invokeAll(tasks);
				} catch (InterruptedException e) {
					throw new RuntimeException(e);
				}
			}

			byte[] validationSerialized = writer.writeValueAsBytes(rootEmployee);
			Employee validationDeserialized = reader.readValue(validationSerialized, Employee.class);

			return Validators.simple("Input vs Deserialized object graph", rootEmployee, validationDeserialized);

		} catch (IOException e) {
			throw new AssertionError(e.getMessage());
		}
	}
}
