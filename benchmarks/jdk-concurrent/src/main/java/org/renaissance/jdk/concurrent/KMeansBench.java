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
    this.forkThreshold = vectorLength / (4 * threadCount) + 1;
  }

 
  public Vector<Double[]> run() throws InterruptedException, ExecutionException {
    final Vector<Double[]> data = generateData(vectorLength);

    final Random random = new Random(100);
    final Vector<Double[]> centroids = randomSample(clusterCount, data, random);

    for (int count = iterationCount; count > 0; count--) {
      final AssignmentTask assignmentTask = new AssignmentTask(data, centroids);
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
  
  final class AssignmentTask extends RecursiveTask<Map<Double[], Vector<Double[]>>> {
    
    private final Vector <Double []> data;

    private final int fromInclusive;

    private final int toExclusive;

    private final int elementCount;
    
    private final Vector <Double []> centroids;
    

    public AssignmentTask(
      final Vector <Double []> data, final Vector <Double []> centroids
    ) {
      this (data, centroids, 0, data.size());
    }
    
    
    public AssignmentTask(
      final Vector <Double []> data, final Vector <Double []> centroids, 
      final int fromInclusive, final int toExclusive
    ) {
      this.data = data;
      this.centroids = centroids;
      this.fromInclusive = fromInclusive;
      this.toExclusive = toExclusive;
      this.elementCount = toExclusive - fromInclusive;
    }

    
    @Override
    protected Map<Double[], Vector<Double[]>> compute() {
      if (elementCount < forkThreshold) {
        return assignToClusters();
        
      } else {
        final int middle = fromInclusive + elementCount / 2;
        final ForkJoinTask<Map<Double[], Vector<Double[]>>> leftTask = 
          new AssignmentTask(data, centroids, fromInclusive, middle).fork();
        final ForkJoinTask<Map<Double[], Vector<Double[]>>> rightTask =
          new AssignmentTask(data, centroids, middle, toExclusive).fork();
        
        return merge(leftTask.join(), rightTask.join());
      }
    }

    
    private Map<Double[], Vector<Double[]>> assignToClusters() {
      final int[] nearestCentroidIndex = findNearestCentroid();
      return collectClusters(nearestCentroidIndex);
    }

   
    private int[] findNearestCentroid() {
      final int[] result = new int[elementCount];

      for (int dataIndex = fromInclusive; dataIndex < toExclusive; dataIndex++) {
        final Double[] element = data.elementAt(dataIndex);
        
        double min = Double.MAX_VALUE;
        for (int centroidIndex = 0; centroidIndex < centroids.size(); centroidIndex++) {
          final double distance = distance(element, centroids.elementAt(centroidIndex));
          if (distance < min) {
            result[dataIndex - fromInclusive] = centroidIndex;
            min = distance;
          }
        }
      }

      return result;
    }

    
    private Map<Double[], Vector<Double[]>> collectClusters(final int[] centroidIndices) {
      final Map<Double[], Vector<Double[]>> result = new HashMap<>();
      for (int dataIndex = 0; dataIndex < centroidIndices.length; dataIndex++) {
        final int centroidIndex = centroidIndices[dataIndex];
      
        final Double[] centroid = centroids.elementAt(centroidIndex);
        final Vector<Double[]> cluster = result.computeIfAbsent(centroid, k -> new Vector<>());
        cluster.add(data.elementAt(dataIndex + fromInclusive));
      }
      
      return result;
    }

    
    private Double distance(final Double[] x, final Double[] y) {
      //
      // Calculates Euclidean distance between the two points. Note that we
      // don't use sqrt(), because sqrt(a) < sqrt(b) <=> a < b.
      //
      double result = 0.0;
      for (int i = 0; i < dimension; i++) {
        result += (x[i] - y[i]) * (x[i] - y[i]);
      }

      return result;
    }
    
    
    private <T> Map<T, Vector<T>> merge(
      final Map<T, Vector<T>> left, final Map<T, Vector<T>> right
    ) {
      final Map<T, Vector<T>> result = new HashMap<>(left);
      
      right.forEach((key, val) -> result.merge(
        key, val, (l, r) -> { l.addAll (r); return l; }
      ));

      return result;
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
        return vectorSum();

      } else {
        final int middle = fromInclusive + elementCount / 2;
        final ForkJoinTask<double[]> leftTask = 
          new VectorSumTask(data, fromInclusive, middle).fork();
        final ForkJoinTask<double[]> rightTask = 
          new VectorSumTask(data, middle, toExclusive).fork();
        return add(leftTask.join(), rightTask.join());
      }
    }


    private double[] add(final double[] x, final double[] y) {
      final double[] result = new double[dimension];

      for (int i = 0; i < dimension; i++) {
        result[i] = x[i] + y[i];
      }
      
      return result;
    }
    

    private double[] vectorSum() {
      final double[] result = new double[dimension];
      
      for (int i = fromInclusive; i < toExclusive; i++) {
        accumulate(data.elementAt(i), result);
      }

      return result;
    }


    private void accumulate(final Double[] val, final double[] acc) {
      for (int i = 0; i < dimension; i++) {
        acc[i] += val[i];
      }
    }
    
  }

}
