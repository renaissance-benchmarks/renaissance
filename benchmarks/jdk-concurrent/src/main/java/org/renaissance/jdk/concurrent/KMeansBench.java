package org.renaissance.jdk.concurrent;


import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Random;
import java.util.Vector;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;
import java.util.concurrent.RecursiveTask;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;


public final class KMeansBench {

  private final int dimension;

  private final int clusterCount;

  private final int iterationCount;
  
  private final int vectorLength;

  private final int threadCount;
  
  private final int forkThreshold;

  //
  
  private final ForkJoinPool forkJoin = new ForkJoinPool();

  
  public KMeansBench(
    int dimension, int vectorLength, int clusterCount,
    int iterationCount, int threadCount
  ) {
    this.dimension = dimension;
    this.vectorLength = vectorLength;
    this.clusterCount = clusterCount;
    this.iterationCount = iterationCount;
    this.threadCount = threadCount;
    this.forkThreshold = vectorLength / (4 * threadCount) + 1;
  }

 
  public Vector<Double[]> run() throws InterruptedException, ExecutionException {
    final Vector<Double[]> data = generateData(vectorLength);

    final Random random = new Random(100);
    final Vector<Double[]> centroids = randomSample(clusterCount, data, random);

    for (int count = iterationCount; count > 0; count--) {
      KMeansTask assignmentTask = new KMeansTask(
        data, centroids, dimension, clusterCount, forkThreshold, threadCount
      );
      
      final UpdateTask updateTask = new UpdateTask(forkJoin.invoke(assignmentTask));
      final Map<Double[], Vector<Double[]>> clusters = forkJoin.invoke(updateTask);
      
      centroids.clear();
      centroids.addAll(clusters.keySet());
    }
    
    forkJoin.awaitQuiescence(1, TimeUnit.SECONDS);
    return centroids;
  }


  private Vector<Double[]> randomSample(
    final int sampleCount, final Vector<Double[]> data, final Random random
  ) {
    return random.ints(sampleCount, 0, data.size()).mapToObj(data::elementAt).collect(
        Vector::new, Vector::add, Vector::addAll
    );
  }


  private Vector<Double[]> generateData(final int count) {
    return IntStream.range(0, count).mapToObj(i -> makeTuple((double) i)).collect(
      Vector::new, Vector::add, Vector::addAll
    );
  }


  private Double[] makeTuple(double base) {
    return new Double[] {
        base, base + 1, base * 4, base * 2, base * 3,
    };
  }
  

  public void tearDown() {
    try {
      forkJoin.shutdown();
      forkJoin.awaitTermination(1, TimeUnit.SECONDS);

    } catch (final InterruptedException ie) {
      throw new RuntimeException (ie);
    }
  }

  //

  final class UpdateTask extends RecursiveTask<Map <Double[], Vector<Double[]>>> {
    
    private final Map <Double [], Vector<Double[]>> clusters;
    
    public UpdateTask(Map <Double [], Vector<Double[]>> clusters) {
      this.clusters = clusters;
    }


    @Override
    protected Map<Double[], Vector<Double[]>> compute() {
      return clusters.values().stream().collect(Collectors.toMap (
          this::average, Function.identity(), (ov, nv) -> nv, HashMap::new
      ));
    }

    
    private Double[] average(final Vector<Double[]> elements) {
      return Arrays.stream(unboxedAverage(elements)).boxed().toArray(Double[]::new);
    }

    
    private double[] unboxedAverage(final Vector<Double[]> elements) {
      final VectorSumTask sumTask = new VectorSumTask(elements);
      final double[] vectorSum = getPool().invoke(sumTask);
      return div(vectorSum, elements.size());
    }

    
    private double[] div(double[] vectorSum, int size) {
      final double[] result = new double[vectorSum.length];
      for (int i = 0; i < vectorSum.length; i++) {
        result[i] = vectorSum[i] / size;
      }

      return result;
    }
    
  }

  //
  
  final class VectorSumTask extends RecursiveTask<double[]> {

    private final Vector<Double[]> data;

    private final int fromInclusive;

    private final int toExclusive;

    private final int elementCount;

    public VectorSumTask(final Vector<Double[]> data) {
      this(data, 0, data.size());
    }

    
    public VectorSumTask(
      final Vector<Double[]> data,
      final int fromInclusive, final int toExclusive
    ) {
      this.data = data;
      this.fromInclusive = fromInclusive;
      this.toExclusive = toExclusive;
      this.elementCount = toExclusive - fromInclusive;
    }

    
    @Override
    protected double[] compute() {
      if (elementCount < forkThreshold) {
        return vectorSum (data, fromInclusive, toExclusive);

      } else {
        final int middle = fromInclusive + elementCount / 2;
        ForkJoinTask<double[]> leftTask = new VectorSumTask(data, fromInclusive, middle).fork();
        ForkJoinTask<double[]> rightTask = new VectorSumTask(data, middle, toExclusive).fork();
        return add(leftTask.join(), rightTask.join());
      }
    }


    private double[] add (final double[] x, final double[] y) {
      final double[] result = new double[dimension];
      for (int i = 0; i < dimension; i++) {
        result [i] = x[i] + y [i];
      }
      
      return result;
    }
    

    private double[] vectorSum(
      final Vector<Double[]> elements,
      final int fromInclusive, final int toExclusive
    ) {
      final double[] result = new double[dimension];
      
      for (int i = fromInclusive; i < toExclusive; i++) {
        accumulate (elements.elementAt(i), result);
      }

      return result;
    }


    private void accumulate (final Double[] val, final double[] acc) {
      for (int i = 0; i < dimension; i++) {
        acc[i] += val[i];
      }
    }
    
  }
  
}
