package org.renaissance.jdk.concurrent;


import java.util.HashMap;
import java.util.Random;
import java.util.Vector;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;
import java.util.concurrent.TimeUnit;


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


    for (int count = iterationCount; count > 0; count--) {
      KMeansTask fff = new KMeansTask(data, centroids, dimension, clusterCount, forkThreshold,
          threadCount);
      
      HashMap<Double[], Vector<Double[]>> clusters = fff.computeClusterAverages(forkJoin.invoke(fff));
      
      centroids.clear();
      centroids.addAll(clusters.keySet());
    }
    
    forkJoin.awaitQuiescence(1, TimeUnit.SECONDS);
    return centroids;
  }
  
  public void tearDown() {
    try {
      forkJoin.shutdown();
      forkJoin.awaitTermination(1, TimeUnit.SECONDS);

    } catch (final InterruptedException ie) {
      throw new RuntimeException (ie);
    }
  }

}
