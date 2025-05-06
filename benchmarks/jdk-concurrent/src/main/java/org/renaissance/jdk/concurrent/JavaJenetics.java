package org.renaissance.jdk.concurrent;

import io.jenetics.Alterer;
import io.jenetics.Chromosome;
import io.jenetics.DoubleChromosome;
import io.jenetics.DoubleGene;
import io.jenetics.Genotype;
import io.jenetics.MonteCarloSelector;
import io.jenetics.Mutator;
import io.jenetics.Selector;
import io.jenetics.SinglePointCrossover;
import io.jenetics.engine.Engine;
import io.jenetics.engine.EvolutionResult;
import io.jenetics.util.Factory;
import io.jenetics.util.MSeq;
import io.jenetics.util.RandomRegistry;

import java.util.Random;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.IntStream;

public final class JavaJenetics {

  private final double geneMinValue;

  private final double geneMaxValue;

  private final int geneCount;

  private final int populationSize;

  private final int generationCount;

  private final int threadCount;

  private final int randomSeed;

  //

  /** Base random seed for other random generators. */
  private final AtomicLong initialSeed = new AtomicLong();

  //

  public JavaJenetics(
    int geneMinValue, int geneMaxValue, int geneCount, int populationSize,
    int generationCount, int threadCount, int randomSeed
  ) {
    this.geneMinValue = geneMinValue;
    this.geneMaxValue = geneMaxValue;
    this.geneCount = geneCount;
    this.populationSize = populationSize;
    this.generationCount = generationCount;
    this.randomSeed = randomSeed;
    this.threadCount = threadCount;
  }

  public void setupBeforeEach() {
    initialSeed.set(randomSeed);
  }


  public Chromosome<DoubleGene> runRepetition(final ExecutorService executor) {
    final CompletableFuture<Chromosome<DoubleGene>> future =
      IntStream.range(0, threadCount).mapToObj(
        i -> CompletableFuture.supplyAsync(this::evolveChromosome, executor)
      ).reduce((f, g) -> f.thenCombine(g, this::average)).get();

    return future.join();
  }


  private Chromosome<DoubleGene> evolveChromosome() {
    //
    // Get a different base seed for each worker thread and create multiple
    // random generators for different GA tasks that are executed concurrently.
    // Tasks can migrate between worker threads, which means that the random
    // generators must be associated with GA tasks to get stable randomness,
    // i.e., they cannot be merely thread-local.
    //
    final long seed = initialSeed.getAndIncrement();

    final Random genotypeRandom = new Random(seed);
    Genotype<DoubleGene> genotype = Genotype.of(DoubleChromosome.of(geneMinValue, geneMaxValue, geneCount));
    Factory<Genotype<DoubleGene>> factory = () -> RandomRegistry.with(genotypeRandom, r -> genotype.newInstance());

    final Random altererRandom = new Random(seed + 15);
    Alterer<DoubleGene, Double> singlePointCrossover = new SinglePointCrossover<DoubleGene, Double>(0.2);
    Alterer<DoubleGene, Double> mutator = new Mutator<DoubleGene, Double>(0.15);
    Alterer<DoubleGene, Double> alterer = Alterer.of(
      (p, g) -> RandomRegistry.with(altererRandom, r -> singlePointCrossover.alter(p, g)),
      (p, g) -> RandomRegistry.with(altererRandom, r -> mutator.alter(p, g))
    );

    final Random offspringRandom = new Random(seed + 7);
    MonteCarloSelector<DoubleGene, Double> offSpringMonteCarloSelector = new MonteCarloSelector();
    Selector<DoubleGene, Double> offSpringSelector = (p, c, o) -> RandomRegistry.with(
      offspringRandom, r -> offSpringMonteCarloSelector.select(p, c, o)
    );

    final Random survivorsRandom = new Random(seed + 11);
    MonteCarloSelector<DoubleGene, Double> survivorsMonteCarloSelector = new MonteCarloSelector();
    Selector<DoubleGene, Double> survivorsSelector = (p, c, o) -> RandomRegistry.with(
      survivorsRandom, r -> survivorsMonteCarloSelector.select(p, c, o)
    );

    final Engine<DoubleGene, Double> engine = Engine.builder(this::fitness, factory)
      .alterers(alterer)
      .offspringSelector(offSpringSelector)
      .survivorsSelector(survivorsSelector)
      .populationSize(populationSize)
      .build();

    final Genotype<DoubleGene> result = engine.stream()
      .limit(generationCount)
      .collect(EvolutionResult.toBestGenotype());

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
