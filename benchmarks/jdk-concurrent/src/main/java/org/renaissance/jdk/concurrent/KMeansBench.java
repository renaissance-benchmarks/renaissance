package org.renaissance.jdk.concurrent;


import java.util.Random;
import java.util.Vector;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;


public final class KMeansBench {

  public static void run(int threadCount, int vectorLength)
      throws InterruptedException, ExecutionException {
    final int dimension = 5;
    int group = 10;
    Vector<Double[]> vec = new Vector<Double[]>(vectorLength);
    Vector<Double[]> vector = new Vector<Double[]>(dimension);
    Random random = new Random(100);
    for (Double j = 0.0; j < vectorLength; j++) {
      vec.add(j.intValue(), new Double[] {
          j, j + 1, j * 4, j * 2, j * 3
      });
    }
    for (int i = 0; i < group; i++) {
      vector.add(i, vec.elementAt(Math.abs(random.nextInt() % vec.size())));
    }

    int forkThreshold = vectorLength / (4 * threadCount) + 1;

    long starttime = System.currentTimeMillis();
    ForkJoinPool fjpool = new ForkJoinPool();
    for (int count = 50; count > 0; count--) {
      KMeansTask fff = new KMeansTask(vec, vector, dimension, group, forkThreshold,
          threadCount);
      fjpool.invoke(fff);
      vector.clear();
      for (int i = fff.getReturnvector().size()
          - 1; i >= 0; i -= (fff.getReturnvector().size() / group)) {
        vector.addElement(fff.getReturnvector().elementAt(i));
      }
    }
    fjpool.shutdown();
    starttime = System.currentTimeMillis() - starttime;
    System.out.println("the execution time is:" + starttime);
  }
}
