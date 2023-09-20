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

  private final double geneMinValue;

  private final double geneMaxValue;

  private final int geneCount;

  private final int chromosomeCount;

  private final int generationCount;

  //

  private final int randomSeed;

  private final int threadCount;

  private final ExecutorService executor = Executors.newWorkStealingPool();

  //

  public JavaJenetics(int geneMinValue, int geneMaxValue, int geneCount, int chromosomeCount,
                      int generationCount, int threadCount, int randomSeed) {
    this.geneMinValue = geneMinValue;
    this.geneMaxValue = geneMaxValue;
    this.geneCount = geneCount;
    this.chromosomeCount = chromosomeCount;
    this.generationCount = generationCount;
    this.randomSeed = randomSeed;
    this.threadCount = threadCount;
  }


  public void setupBeforeAll() {
    RandomRegistry.random(new Random(randomSeed));
  }


  public void tearDownAfterAll() {
    executor.shutdown();

    try {
      executor.awaitTermination(1, TimeUnit.SECONDS);

    } catch (final InterruptedException e) {
      throw new RuntimeException(e);
    }
  }


  public Object runRepetition() {
    final CompletableFuture<Chromosome<DoubleGene>> future =
      IntStream.range(0, threadCount).mapToObj(
        i -> CompletableFuture.supplyAsync(this::evolveChromosome, executor)
      ).reduce((f, g) -> f.thenCombine(g, this::average)).get();

    final Chromosome<DoubleGene> result = future.join();
    System.out.println(result.get(0) + ", " + result.get(1));
    return result;
  }


  private Chromosome<DoubleGene> evolveChromosome() {
    final Factory<Genotype<DoubleGene>> factory = Genotype.of(
      DoubleChromosome.of(geneMinValue, geneMaxValue, geneCount)
    );

    final Engine<DoubleGene, Double> engine = Engine.builder(this::fitness, factory)
      .selector(new MonteCarloSelector<>()).populationSize(chromosomeCount).build();

    final Genotype<DoubleGene> result = engine.stream()
      .limit(generationCount).collect(EvolutionResult.toBestGenotype());

    return result.chromosome();
  }


  private Double fitness(final Genotype<DoubleGene> g) {
    final Chromosome<DoubleGene> c = g.chromosome();
    final double x = c.get(0).doubleValue() - 10;
    final double y = c.get(1).doubleValue() - 15;
    return -x * x - y * y;
  }


  private Chromosome<DoubleGene> average(
    final Chromosome<DoubleGene> ca, final Chromosome<DoubleGene> cb
  ) {
    return DoubleChromosome.of(
      IntStream.range(0, ca.length())
        .mapToObj(i -> ca.get(i).mean(cb.get(i)))
        .collect(MSeq.toMSeq())
    );
  }

}
