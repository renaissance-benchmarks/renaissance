package org.renaissance.jdk.concurrent;


import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Vector;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.ForkJoinTask;
import java.util.concurrent.RecursiveTask;
import java.util.concurrent.TimeUnit;
import java.util.stream.IntStream;


public final class JavaKMeans {

  private final int dimension;

  private final int clusterCount;

  private final int iterationCount;

  private final int vectorLength;

  private final int forkThreshold;

  //

  private final ForkJoinPool forkJoin = new ForkJoinPool();


  public JavaKMeans(
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

    for (int iteration = 0; iteration < iterationCount; iteration++) {
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
    return IntStream.range(0, count).mapToObj(i -> makeTuple(i)).collect(
      Vector::new, Vector::add, Vector::addAll
    );
  }


  private Double[] makeTuple(double base) {
    // TODO This needs to take dimension into account!
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


  private static <T> Map<T, Vector<T>> merge(
    final Map<T, Vector<T>> left, final Map<T, Vector<T>> right
  ) {
    final Map<T, Vector<T>> result = new HashMap<>(left);

    right.forEach((key, val) -> result.merge(
        key, val, (l, r) -> { l.addAll(r); return l; }
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

  final class AssignmentTask extends RangedTask<Map<Double[], Vector<Double[]>>> {

    private final Vector<Double[]> data;

    private final Vector<Double[]> centroids;


    public AssignmentTask(
      final Vector<Double[]> data, final Vector<Double[]> centroids
    ) {
      this(data, centroids, 0, data.size());
    }


    private AssignmentTask(
      final Vector<Double[]> data, final Vector<Double[]> centroids,
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
    protected Map<Double[], Vector<Double[]>> computeDirectly() {
      return collectClusters(findNearestCentroid());
    }


    private Map<Double[], Vector<Double[]>> collectClusters(final int[] centroidIndices) {
      final Map<Double[], Vector<Double[]>> result = new HashMap<>();

      for (int dataIndex = fromInclusive; dataIndex < toExclusive; dataIndex++) {
        final int centroidIndex = centroidIndices[dataIndex - fromInclusive];
        final Double[] centroid = centroids.elementAt(centroidIndex);
        final Double[] element = data.elementAt(dataIndex);
        result.computeIfAbsent(centroid, k -> new Vector<>()).add(element);
      }

      return result;
    }


    private int[] findNearestCentroid() {
      final int[] result = new int[taskSize];

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
    protected ForkJoinTask<Map<Double[], Vector<Double[]>>> createSubtask(
      final int fromInclusive, final int toExclusive
    ) {
      return new AssignmentTask(data, centroids, fromInclusive, toExclusive);
    }


    @Override
    protected Map<Double[], Vector<Double[]>> combineResults(
      final Map<Double[], Vector<Double[]>> left, final Map<Double[], Vector<Double[]>> right
    ) {
      return merge(left, right);
    }

  }

  //

  final class UpdateTask extends RangedTask<Map<Double[], Vector<Double[]>>> {

    private final List<Vector<Double[]>> clusters;


    public UpdateTask(final Map<Double[], Vector<Double[]>> clusters) {
      this(new ArrayList<>(clusters.values()));
    }


    public UpdateTask(final List<Vector<Double[]>> clusters) {
      this(clusters, 0, clusters.size());
    }


    private UpdateTask(
      final List<Vector<Double[]>> clusters,
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
    protected Map<Double[], Vector<Double[]>> computeDirectly() {
      return computeClusterAverages();
    }


    private Map<Double[], Vector<Double[]>> computeClusterAverages() {
      final Map<Double[], Vector<Double[]>> result = new HashMap<>();

      for (int clusterIndex = fromInclusive; clusterIndex < toExclusive; clusterIndex++) {
        final Vector<Double[]> clusterElements = clusters.get(clusterIndex);
        final Double[] clusterAverage = boxed(average(clusterElements));
        result.put(clusterAverage, clusterElements);
      }

      return result;
    }


    private Double[] boxed(final double[] values) {
      return Arrays.stream(values).boxed().toArray(Double[]::new);
    }


    private double[] average(final Vector<Double[]> elements) {
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
    protected ForkJoinTask<Map<Double[], Vector<Double[]>>> createSubtask(
      final int fromInclusive, final int toExclusive
    ) {
      return new UpdateTask(clusters, fromInclusive, toExclusive);
    }


    @Override
    protected Map<Double[], Vector<Double[]>> combineResults(
      final Map<Double[], Vector<Double[]>> left, final Map<Double[], Vector<Double[]>> right
    ) {
      return merge(left, right);
    }

  }

  //

  final class VectorSumTask extends RangedTask<double[]> {

    private final Vector<Double[]> data;


    public VectorSumTask(final Vector<Double[]> data) {
      this(data, 0, data.size());
    }


    private VectorSumTask(
      final Vector<Double[]> data,
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
        accumulate(data.elementAt(i), result);
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
