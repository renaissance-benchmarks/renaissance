package org.renaissance.jdk.concurrent;


import java.util.Random;
import java.util.Vector;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ForkJoinPool;


public class KMeansBench {

  public static void run(int numThreads, int vectorLength)
      throws InterruptedException, ExecutionException {
    boolean bool = false;
    final int demision = 5;
    int group = 10;
    Vector<Double[]> vec = new Vector<Double[]>(vectorLength);
    Vector<Double[]> vector = new Vector<Double[]>(demision);
    Random random = new Random(100);
    for (Double j = 0.0; j < vectorLength; j++) {
      vec.add(j.intValue(), new Double[] {
          j, j + 1, j * 4, j * 2, j * 3
      });
    }
    for (int i = 0; i < group; i++) {
      vector.add(i, vec.elementAt(Math.abs(random.nextInt() % vec.size())));
    }

    int Threshold = vectorLength / (4 * numThreads) + 1;

    long starttime = System.currentTimeMillis();
    ForkJoinPool fjpool = new ForkJoinPool();
    for (int count = 50; count > 0; count--) {
      KMeansFork fff = new KMeansFork(vec, vector, demision, group, Threshold,
          numThreads);
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
