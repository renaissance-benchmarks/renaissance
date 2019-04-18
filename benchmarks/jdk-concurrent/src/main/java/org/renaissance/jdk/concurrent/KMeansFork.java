package org.renaissance.jdk.concurrent;


import java.util.HashMap;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Vector;
import java.util.concurrent.RecursiveTask;


public final class KMeansFork extends RecursiveTask<HashMap<Double[], Vector<Double[]>>> {

  private int Threshold;

  private final int demision;

  private int group;

  private int numthreads;

  private Vector<Double[]> vec;

  private Vector<Double[]> vector;

  private Vector<Double[]> returnvector = new Vector<Double[]>();

  public KMeansFork(Vector<Double[]> vec, Vector<Double[]> vector, int demision,
      int group, int Threshold, int numthreads) {
    this.demision = demision;
    this.group = group;
    this.vec = vec;
    this.vector = vector;
    this.Threshold = Threshold;
    this.numthreads = numthreads;
  }

  public HashMap<Double[], Vector<Double[]>> Iteration(Vector<Double[]> vec) {
    Double distance = 0.0;
    int[] ClusterNumber = new int[vec.size()];
    for (int i = vec.size() - 1; i >= 0; i--) {
      Double min = Double.MAX_VALUE;
      for (int j = vector.size() - 1; j >= 0; j--) {
        distance = sumDistance(vec.elementAt(i), vec.elementAt(j));
        if (distance < min) {
          min = distance;
          ClusterNumber[i] = j;
        }
      }
    }
    return computerCluster(ClusterNumber, vec, vector);
  }
  public HashMap<Double[], Vector<Double[]>> computerCluster(int[] clu,
      Vector<Double[]> temprec, Vector<Double[]> tempvector) {
    HashMap<Double[], Vector<Double[]>> map = new HashMap<Double[], Vector<Double[]>>();
    for (int i = clu.length - 1; i >= 0; i--) {
      if (!map.containsKey(temprec.elementAt(clu[i]))) {
        Vector<Double[]> clusterVec = new Vector<Double[]>();
        clusterVec.add(temprec.elementAt(i));
        map.put(temprec.elementAt(clu[i]), clusterVec);
      } else {

        map.get(temprec.elementAt(clu[i])).add(temprec.elementAt(clu[i]));
      }
    }
    return map;
  }

  public Double sumDistance(Double[] x, Double[] y) {
    Double sum = 0.0;
    for (int i = demision - 1; i >= 0; i--) {
      sum += (x[i] - y[i]) * (x[i] - y[i]);
    }
    return sum;
  }
  public Double[] average(Double[] x, Double[] y) {
    Double[] aver = new Double[demision];
    for (int i = demision - 1; i >= 0; i--) {
      aver[i] = (x[i] + y[i]);
    }
    return aver;
  }

  public HashMap<Double[], Vector<Double[]>> ComputerAver(
      HashMap<Double[], Vector<Double[]>> avermap) {

    Iterator<Entry<Double[], Vector<Double[]>>> averiter = avermap.entrySet().iterator();
    HashMap<Double[], Vector<Double[]>> computerMap = new HashMap<Double[], Vector<Double[]>>();
    int count = 0;
    while (averiter.hasNext()) {
      Entry<Double[], Vector<Double[]>> entry = averiter.next();
      Vector<Double[]> itervec = entry.getValue();
      Double[] averagemeans = new Double[demision];
      for (int i = demision - 1; i >= 0; i--) {
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
    int hel = vec.size();
    if (hel < Threshold) {
      return Iteration(vec);
    } else {
      int veclength = vec.size();
      int middle = veclength / 2;
      Vector<Double[]> vectorone = new Vector<Double[]>(middle);
      for (int i = 0; i < middle; i++) {
        vectorone.add(i, vec.elementAt(i));
      }
      Vector<Double[]> vectortwo = new Vector<Double[]>(veclength - middle);
      for (int i = middle; i < vec.size(); i++) {
        vectortwo.add((i - middle), vec.elementAt(i));
      }
      KMeansFork kmeansone = new KMeansFork(vectorone, vector, demision, group, Threshold,
          numthreads);
      KMeansFork kmeanstwo = new KMeansFork(vectortwo, vector, demision, group, Threshold,
          numthreads);
      kmeansone.fork();
      kmeanstwo.fork();
      HashMap<Double[], Vector<Double[]>> leftmap = kmeansone.join();
      HashMap<Double[], Vector<Double[]>> rightmap = kmeanstwo.join();
      Iterator<Entry<Double[], Vector<Double[]>>> iter = leftmap.entrySet().iterator();
      while (iter.hasNext()) {
        Entry<Double[], Vector<Double[]>> entry = iter.next();
        Double[] key = (Double[]) entry.getKey();
        Vector<Double[]> itervec = entry.getValue();
        if (rightmap.get(key) != null) {
          Vector<Double[]> tempvecone = rightmap.get(key);
          int num = tempvecone.size();
          for (int i = 0; i < itervec.size(); i++) {
            tempvecone.addElement(itervec.elementAt(i + num));
          }
          rightmap.put(key, tempvecone);
        } else {
          rightmap.put(key, itervec);
        }
      }
      return ComputerAver(rightmap);
    }
  }

  public Vector<Double[]> getReturnvector() {
    return returnvector;
  }
}
