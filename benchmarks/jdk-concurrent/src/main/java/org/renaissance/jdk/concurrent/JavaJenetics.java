package org.renaissance.jdk.concurrent;

import java.util.Random;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.stream.IntStream;

import io.jenetics.Chromosome;
import io.jenetics.DoubleChromosome;
import io.jenetics.DoubleGene;
import io.jenetics.Genotype;
import io.jenetics.MonteCarloSelector;
import io.jenetics.engine.Engine;
import io.jenetics.engine.EvolutionResult;
import io.jenetics.util.Factory;
import io.jenetics.util.MSeq;
import io.jenetics.util.RandomRegistry;

public final class JavaJenetics {

  private static final double GENE_MIN_VALUE = -2000;

  private static final double GENE_MAX_VALUE = 2000;

  private static final int GENE_COUNT = 200;

  private static final int CHROMOSOME_COUNT = 50;

  private static final int GENERATION_COUNT = 5000;

  //

  private static final int RANDOM_SEED = 7;

  private static final int THREAD_COUNT = 2;

  private final ExecutorService executor = Executors.newWorkStealingPool();

  //

  public JavaJenetics() {}

  public void setupBeforeAll() {
    RandomRegistry.setRandom(new Random(RANDOM_SEED));
  }

  public void tearDownAfterAll() {
    executor.shutdown();

    try {
      executor.awaitTermination(1, TimeUnit.SECONDS);

    } catch (final InterruptedException e) {
      throw new RuntimeException(e);
    }
  }

  public Object runIteration() {
    final CompletableFuture<Chromosome<DoubleGene>> future =
        IntStream.range(0, THREAD_COUNT)
            .mapToObj(i -> CompletableFuture.supplyAsync(this::evolveChromosome, executor))
            .reduce((f, g) -> f.thenCombine(g, this::average))
            .get();

    final Chromosome<DoubleGene> result = future.join();
    System.out.println(result.getGene(0) + ", " + result.getGene(1));
    return result;
  }

  private Chromosome<DoubleGene> evolveChromosome() {
    final Factory<Genotype<DoubleGene>> factory =
        Genotype.of(DoubleChromosome.of(GENE_MIN_VALUE, GENE_MAX_VALUE, GENE_COUNT));

    final Engine<DoubleGene, Double> engine =
        Engine.builder(this::fitness, factory)
            .selector(new MonteCarloSelector<>())
            .populationSize(CHROMOSOME_COUNT)
            .build();

    final Genotype<DoubleGene> result =
        engine.stream().limit(GENERATION_COUNT).collect(EvolutionResult.toBestGenotype());

    return result.getChromosome();
  }

  private Double fitness(final Genotype<DoubleGene> g) {
    final Chromosome<DoubleGene> c = g.getChromosome();
    final double x = c.getGene(0).doubleValue() - 10;
    final double y = c.getGene(1).doubleValue() - 15;
    return -x * x - y * y;
  }

  private Chromosome<DoubleGene> average(
      final Chromosome<DoubleGene> ca, final Chromosome<DoubleGene> cb) {
    return DoubleChromosome.of(
        IntStream.range(0, ca.length())
            .mapToObj(i -> ca.getGene(i).mean(cb.getGene(i)))
            .collect(MSeq.toMSeq()));
  }
}
