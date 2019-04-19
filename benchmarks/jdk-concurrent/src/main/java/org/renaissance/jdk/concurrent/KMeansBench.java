package org.renaissance.jdk.concurrent;


import java.util.HashMap;
import java.util.Random;
import java.util.Vector;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;


public final class KMeansBench {
  private final int dimension;

  private final int clusterCount;

  private final int iterationCount;
  
  private final int vectorLength;

  private final int threadCount;
  
  public KMeansBench(
    int dimension, int vectorLength, int clusterCount,
    int iterationCount, int threadCount
  ) {
    this.dimension = dimension;
    this.vectorLength = vectorLength;
    this.clusterCount = clusterCount;
    this.iterationCount = iterationCount;
    this.threadCount = threadCount;
  }

 
  public void run() throws InterruptedException, ExecutionException {
    Vector<Double[]> data = new Vector<Double[]>(vectorLength);
    Vector<Double[]> centroids = new Vector<Double[]>(dimension);
    Random random = new Random(100);
    for (Double j = 0.0; j < vectorLength; j++) {
      data.add(j.intValue(), new Double[] {
          j, j + 1, j * 4, j * 2, j * 3
      });
    }
    for (int i = 0; i < clusterCount; i++) {
      centroids.add(i, data.elementAt(Math.abs(random.nextInt() % data.size())));
    }

    int forkThreshold = vectorLength / (4 * threadCount) + 1;

    long starttime = System.currentTimeMillis();
    ForkJoinPool fjpool = new ForkJoinPool();
    for (int count = iterationCount; count > 0; count--) {
      KMeansTask fff = new KMeansTask(data, centroids, dimension, clusterCount, forkThreshold,
          threadCount);
      
      HashMap<Double[], Vector<Double[]>> clusters = fff.computeClusterAverages(fjpool.invoke(fff));
      
      centroids.clear();
      centroids.addAll(clusters.keySet());
    }
    fjpool.shutdown();
    starttime = System.currentTimeMillis() - starttime;
    System.out.println("the execution time is:" + starttime);
  }
}
