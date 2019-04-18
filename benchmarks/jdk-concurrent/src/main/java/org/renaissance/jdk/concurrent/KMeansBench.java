package org.renaissance.jdk.concurrent;


import java.util.Random;
import java.util.Vector;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;


public final class KMeansBench {

  public static void run(int threadCount, int vectorLength)
      throws InterruptedException, ExecutionException {
    final int dimension = 5;
    int clusterCount = 10;
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
    for (int count = 50; count > 0; count--) {
      KMeansTask fff = new KMeansTask(data, centroids, dimension, clusterCount, forkThreshold,
          threadCount);
      fjpool.invoke(fff);
      centroids.clear();
      for (int i = fff.getReturnvector().size()
          - 1; i >= 0; i -= (fff.getReturnvector().size() / clusterCount)) {
        centroids.addElement(fff.getReturnvector().elementAt(i));
      }
    }
    fjpool.shutdown();
    starttime = System.currentTimeMillis() - starttime;
    System.out.println("the execution time is:" + starttime);
  }
}
