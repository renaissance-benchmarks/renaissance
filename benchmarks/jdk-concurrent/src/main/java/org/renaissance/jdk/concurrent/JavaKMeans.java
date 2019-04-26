package org.renaissance.jdk.concurrent;


import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;
import java.util.concurrent.RecursiveTask;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;
import java.util.stream.IntStream;


public final class JavaKMeans {

  private final int dimension;

  private final int forkThreshold;

  //

  private final ForkJoinPool forkJoin;


  public JavaKMeans(final int dimension, final int threadCount) {
    this.dimension = dimension;
    // Try to (roughly) fit fork data into half the L2 cache. 
    this.forkThreshold = forkThreshold(dimension, (256 / 2) * 1024);
    this.forkJoin = new ForkJoinPool(threadCount);
  }


  private int forkThreshold(final int dimension, final int sizeLimit) {
    final int doubleSize = 8 + Double.BYTES; 
	final int pointerSize = Long.BYTES;
	final int arraySize = 8 + Integer.BYTES + dimension * pointerSize;
	final int elementSize = arraySize + dimension * doubleSize;
	return sizeLimit / (elementSize + pointerSize);
  }


  public List<Double[]> run(
    final int clusterCount, final List <Double[]> data, final int iterationCount
  ) throws InterruptedException, ExecutionException {
    List<Double[]> centroids = randomSample(clusterCount, data, new Random(100));
    for (int iteration = 0; iteration < iterationCount; iteration++) {
      final AssignmentTask assignmentTask = new AssignmentTask(data, centroids);
      final UpdateTask updateTask = new UpdateTask(forkJoin.invoke(assignmentTask));
      final Map<Double[], List<Double[]>> clusters = forkJoin.invoke(updateTask);

      centroids = new ArrayList<>(clusters.keySet());
    }

    forkJoin.awaitQuiescence(1, TimeUnit.SECONDS);
    return centroids;
  }


  private List<Double[]> randomSample(
    final int sampleCount, final List<Double[]> data, final Random random
  ) {
    return random.ints(sampleCount, 0, data.size())
      .mapToObj(data::get).collect(Collectors.toList());
  }


  static List<Double[]> generateData(
	final int count, final int dimension, final int clusterCount
  ) {
	// Create random generators for individual dimensions.
    final Random[] randoms = IntStream.range(0, dimension).mapToObj(
	  d -> new Random  (1 + 2 * d)
    ).toArray(Random[]::new);
    
    // Generate random data for all dimensions.
    return IntStream.range(0, count).mapToObj(i -> {
  	  return IntStream.range(0, dimension).mapToObj(d ->
  		(((i + (1 + 2 * d)) % clusterCount) * 1.0 / clusterCount) + randoms[d].nextDouble() * 0.5
  	  ).toArray(Double[]::new);
    }).collect(Collectors.toList());
  }


  public void tearDown() {
    try {
      forkJoin.shutdown();
      forkJoin.awaitTermination(1, TimeUnit.SECONDS);

    } catch (final InterruptedException ie) {
      throw new RuntimeException (ie);
    }
  }


  private static <T> Map<T, List<T>> merge(
    final Map<T, List<T>> left, final Map<T, List<T>> right
  ) {
    //
    // When merging values with the same key, create a new ArrayList to avoid
    // modifying an existing list representing a value in another HashMap.
    //
    final Map<T, List<T>> result = new HashMap<>(left);

    right.forEach((key, val) -> result.merge(
      key, val, (l, r) -> {
        final List<T> m = new ArrayList<>(l);
        m.addAll(r);
        return m;
      }
    ));

    return result;
  }

  //

  abstract class RangedTask<V> extends RecursiveTask<V> {

    protected final int fromInclusive;

    protected final int toExclusive;

    protected final int taskSize;


    protected RangedTask(
      final int fromInclusive, final int toExclusive
    ) {
      this.fromInclusive = fromInclusive;
      this.toExclusive = toExclusive;
      this.taskSize = toExclusive - fromInclusive;
    }


    @Override
    protected V compute() {
      if (taskSize < forkThreshold()) {
        return computeDirectly();

      } else {
        final int middle = fromInclusive + taskSize / 2;
        final ForkJoinTask<V> leftTask = createSubtask(fromInclusive, middle).fork();
        final ForkJoinTask<V> rightTask = createSubtask(middle, toExclusive).fork();
        return combineResults(leftTask.join(), rightTask.join());
      }
    }

    //

    protected abstract int forkThreshold();

    protected abstract V computeDirectly();

    protected abstract ForkJoinTask<V> createSubtask(
      final int fromInclusive, final int toExclusive
    );

    protected abstract V combineResults(final V left, final V right);
  }

  //

  final class AssignmentTask extends RangedTask<Map<Double[], List<Double[]>>> {

    private final List<Double[]> data;

    private final List<Double[]> centroids;


    public AssignmentTask(
      final List<Double[]> data, final List<Double[]> centroids
    ) {
      this(data, centroids, 0, data.size());
    }


    private AssignmentTask(
      final List<Double[]> data, final List<Double[]> centroids,
      final int fromInclusive, final int toExclusive
    ) {
      super(fromInclusive, toExclusive);
      this.data = data;
      this.centroids = centroids;
    }

    //

    @Override
    protected int forkThreshold() {
      return forkThreshold;
    }


    @Override
    protected Map<Double[], List<Double[]>> computeDirectly() {
      return collectClusters(findNearestCentroid());
    }


    private Map<Double[], List<Double[]>> collectClusters(final int[] centroidIndices) {
      final Map<Double[], List<Double[]>> result = new HashMap<>();

      for (int dataIndex = fromInclusive; dataIndex < toExclusive; dataIndex++) {
        final int centroidIndex = centroidIndices[dataIndex - fromInclusive];
        final Double[] centroid = centroids.get(centroidIndex);
        final Double[] element = data.get(dataIndex);
        result.computeIfAbsent(centroid, k -> new ArrayList<>()).add(element);
      }

      return result;
    }


    private int[] findNearestCentroid() {
      final int[] result = new int[taskSize];

      for (int dataIndex = fromInclusive; dataIndex < toExclusive; dataIndex++) {
        final Double[] element = data.get(dataIndex);

        double min = Double.MAX_VALUE;
        for (int centroidIndex = 0; centroidIndex < centroids.size(); centroidIndex++) {
          final double distance = distance(element, centroids.get(centroidIndex));
          if (distance < min) {
            result[dataIndex - fromInclusive] = centroidIndex;
            min = distance;
          }
        }
      }

      return result;
    }


    private double distance(final Double[] x, final Double[] y) {
      //
      // Calculates Euclidean distance between the two points. Note that we
      // don't use sqrt(), because sqrt(a) < sqrt(b) <=> a < b.
      //
      double result = 0.0;
      for (int i = 0; i < dimension; i++) {
        final double diff = x[i] - y[i];
        result += diff * diff;
      }

      return result;
    }


    @Override
    protected ForkJoinTask<Map<Double[], List<Double[]>>> createSubtask(
      final int fromInclusive, final int toExclusive
    ) {
      return new AssignmentTask(data, centroids, fromInclusive, toExclusive);
    }


    @Override
    protected Map<Double[], List<Double[]>> combineResults(
      final Map<Double[], List<Double[]>> left, final Map<Double[], List<Double[]>> right
    ) {
      return merge(left, right);
    }

  }

  //

  final class UpdateTask extends RangedTask<Map<Double[], List<Double[]>>> {

    private final List<List<Double[]>> clusters;


    public UpdateTask(final Map<Double[], List<Double[]>> clusters) {
      this(new ArrayList<>(clusters.values()));
    }


    public UpdateTask(final List<List<Double[]>> clusters) {
      this(clusters, 0, clusters.size());
    }


    private UpdateTask(
      final List<List<Double[]>> clusters,
      final int fromInclusive, final int toExclusive
    ) {
      super(fromInclusive, toExclusive);
      this.clusters = clusters;
    }

    //

    @Override
    protected int forkThreshold() {
      return 2;
    }


    @Override
    protected Map<Double[], List<Double[]>> computeDirectly() {
      return computeClusterAverages();
    }


    private Map<Double[], List<Double[]>> computeClusterAverages() {
      final Map<Double[], List<Double[]>> result = new HashMap<>();

      for (int clusterIndex = fromInclusive; clusterIndex < toExclusive; clusterIndex++) {
        final List<Double[]> clusterElements = clusters.get(clusterIndex);
        final Double[] clusterAverage = boxed(average(clusterElements));
        result.put(clusterAverage, clusterElements);
      }

      return result;
    }


    private Double[] boxed(final double[] values) {
      return Arrays.stream(values).boxed().toArray(Double[]::new);
    }


    private double[] average(final List<Double[]> elements) {
      final VectorSumTask sumTask = new VectorSumTask(elements);
      final double[] vectorSums = getPool().invoke(sumTask);
      return div(vectorSums, elements.size());
    }


    private double[] div(double[] values, int divisor) {
      final double[] result = new double[values.length];
      for (int i = 0; i < values.length; i++) {
        result[i] = values[i] / divisor;
      }

      return result;
    }


    @Override
    protected ForkJoinTask<Map<Double[], List<Double[]>>> createSubtask(
      final int fromInclusive, final int toExclusive
    ) {
      return new UpdateTask(clusters, fromInclusive, toExclusive);
    }


    @Override
    protected Map<Double[], List<Double[]>> combineResults(
      final Map<Double[], List<Double[]>> left, final Map<Double[], List<Double[]>> right
    ) {
      return merge(left, right);
    }

  }

  //

  final class VectorSumTask extends RangedTask<double[]> {

    private final List<Double[]> data;


    public VectorSumTask(final List<Double[]> data) {
      this(data, 0, data.size());
    }


    private VectorSumTask(
      final List<Double[]> data,
      final int fromInclusive, final int toExclusive
    ) {
      super(fromInclusive, toExclusive);
      this.data = data;
    }

    //

    @Override
    protected int forkThreshold() {
      return forkThreshold;
    }


    @Override
    protected double[] computeDirectly() {
      return vectorSum();
    }


    private double[] vectorSum() {
      final double[] result = new double[dimension];

      for (int i = fromInclusive; i < toExclusive; i++) {
        accumulate(data.get(i), result);
      }

      return result;
    }


    private void accumulate(final Double[] val, final double[] acc) {
      for (int i = 0; i < dimension; i++) {
        acc[i] += val[i];
      }
    }


    @Override
    protected ForkJoinTask<double[]> createSubtask(int fromInclusive, int toExclusive) {
      return new VectorSumTask(data, fromInclusive, toExclusive);
    }


    @Override
    protected double[] combineResults(final double[] left, final double[] right) {
      return add(left, right);
    }


    private double[] add(final double[] x, final double[] y) {
      final double[] result = new double[dimension];

      for (int i = 0; i < dimension; i++) {
        result[i] = x[i] + y[i];
      }

      return result;
    }

  }

}
