package org.renaissance.jdk.concurrent;


import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Vector;
import java.util.concurrent.RecursiveTask;


public final class KMeansTask extends RecursiveTask<HashMap<Double[], Vector<Double[]>>> {

  private final int forkThreshold;

  private final int dimension;

  private final int clusterCount;

  private final int threadCount;

  private final Vector<Double[]> data;

  private final Vector<Double[]> centroids;

  private final Vector<Double[]> returnvector = new Vector<Double[]>();

  public KMeansTask(Vector<Double[]> data, Vector<Double[]> centroids, int dimension,
      int clusterCount, int forkThreshold, int threadCount) {
    this.dimension = dimension;
    this.clusterCount = clusterCount;
    this.data = data;
    this.centroids = centroids;
    this.forkThreshold = forkThreshold;
    this.threadCount = threadCount;
  }

  public HashMap<Double[], Vector<Double[]>> computeDirectly(Vector<Double[]> data) {
    int[] nearestCentroidIndex = assignToNearestCentroid(data);
    return collectClusters(nearestCentroidIndex, data, centroids);
  }

  private int[] assignToNearestCentroid(Vector<Double[]> data) {
    int[] result = new int[data.size()];

    for (int dataIndex = 0; dataIndex < data.size(); dataIndex++) {
      final Double[] element = data.elementAt(dataIndex);
      
      double min = Double.MAX_VALUE;
      for (int centroidIndex = 0; centroidIndex < centroids.size(); centroidIndex++) {
        final double distance = distance(element, centroids.elementAt(centroidIndex));
        if (distance < min) {
          result[dataIndex] = centroidIndex;
          min = distance;
        }
      }
    }

    return result;
  }


  public HashMap<Double[], Vector<Double[]>> collectClusters(
    int[] nearestCentroidIndex, Vector<Double[]> data, Vector<Double[]> centroids
  ) {
    final HashMap<Double[], Vector<Double[]>> result = new HashMap<>();
    for (int dataIndex = 0; dataIndex < nearestCentroidIndex.length; dataIndex++) {
      final int centroidIndex = nearestCentroidIndex[dataIndex];
      final Double[] centroid = centroids.elementAt(centroidIndex);
      final Vector<Double[]> cluster = result.computeIfAbsent(centroid, k -> new Vector<>());
      cluster.add(data.elementAt(dataIndex));
    }
    
    return result;
  }

  private Double distance(Double[] x, Double[] y) {
    //
    // Calculates Euclidean distance between the two points. Note that we
    // don't use sqrt(), because if sqrt(a) < sqrt(b), then also a < b.
    //
    double result = 0.0;
    for (int i = 0; i < dimension; i++) {
      result += (x[i] - y[i]) * (x[i] - y[i]);
    }
    
    return result;
  }
  public Double[] average(Double[] x, Double[] y) {
    Double[] aver = new Double[dimension];
    for (int i = dimension - 1; i >= 0; i--) {
      aver[i] = (x[i] + y[i]);
    }
    return aver;
  }

  public HashMap<Double[], Vector<Double[]>> computeClusterAverages(
      HashMap<Double[], Vector<Double[]>> avermap) {

    Iterator<Entry<Double[], Vector<Double[]>>> averiter = avermap.entrySet().iterator();
    HashMap<Double[], Vector<Double[]>> computerMap = new HashMap<>();
    int count = 0;
    while (averiter.hasNext()) {
      Entry<Double[], Vector<Double[]>> entry = averiter.next();
      Vector<Double[]> itervec = entry.getValue();
      Double[] averagemeans = new Double[dimension];
      for (int i = dimension - 1; i >= 0; i--) {
        int aversize = itervec.size() - 1;
        Double sum = 0.0;
        while (aversize >= 0) {
          sum += itervec.elementAt(aversize)[i];
          aversize--;
        }
        averagemeans[i] = sum / itervec.size();
      }
      returnvector.add(count++, averagemeans);
      computerMap.put(averagemeans, itervec);
    }
    return computerMap;
  }

  @Override
  protected HashMap<Double[], Vector<Double[]>> compute() {
    if (data.size() < forkThreshold) {
      return computeDirectly(data);
      
    } else {
      int veclength = data.size();
      int middle = veclength / 2;
      
      Vector<Double[]> leftVector = new Vector<Double[]>(middle);
      for (int i = 0; i < middle; i++) {
        leftVector.add(i, data.elementAt(i));
      }
      
      Vector<Double[]> rightVector = new Vector<Double[]>(veclength - middle);
      for (int i = middle; i < data.size(); i++) {
        rightVector.add((i - middle), data.elementAt(i));
      }
      
      KMeansTask leftTask = new KMeansTask(leftVector, centroids, dimension, clusterCount, forkThreshold,
          threadCount);
      KMeansTask rightTask = new KMeansTask(rightVector, centroids, dimension, clusterCount, forkThreshold,
          threadCount);
      leftTask.fork();
      rightTask.fork();
      
      HashMap <Double[], Vector <Double []>> result = merge(leftTask.join(), rightTask.join());
      return computeClusterAverages(result);
    }
  }

  private <T> HashMap<T, Vector<T>> merge(
    final Map<T, Vector<T>> left, final Map<T, Vector<T>> right
  ) {
    final HashMap<T, Vector<T>> result = new HashMap<>(left);
    
    right.forEach((k, v) -> result.merge(
      k, v, (l, r) -> { l.addAll (r); return l; }
    ));

    return result;
  }

  public Vector<Double[]> getReturnvector() {
    return returnvector;
  }
}
