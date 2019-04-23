package org.renaissance.jdk.concurrent;


import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Vector;
import java.util.concurrent.RecursiveTask;


public class KMeansTask extends RecursiveTask<HashMap<Double[], Vector<Double[]>>> {

  private int Threshold;
  private final int demision;
  private int group;
  private int numthreads;
  private Vector<Double[]> vec;
  private Vector<Double[]> vector;
  private Vector<Double[]> returnVector = new Vector<Double[]>();

  public KMeansTask(Vector<Double[]> vec, Vector<Double[]> vector, int demision, int group, int Threshold, int numthreads) {
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

  public HashMap<Double[], Vector<Double[]>> computerCluster(int[] clu, Vector<Double[]> temprec, Vector<Double[]> tempvector) {
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

  public HashMap<Double[], Vector<Double[]>> ComputerAver(HashMap<Double[], Vector<Double[]>> avermap) {

    Iterator averiter = avermap.entrySet().iterator();
    HashMap<Double[], Vector<Double[]>> computerMap = new HashMap<Double[], Vector<Double[]>>();
    int count = 0;
    while (averiter.hasNext()) {
      Map.Entry entry = (Map.Entry) averiter.next();
      Double[] key = (Double[]) entry.getKey();
      Vector<Double[]> itervec = (Vector<Double[]>) entry.getValue();
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
      returnVector.add(count++, averagemeans);
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
      Vector<Double[]> vectorOne = new Vector<Double[]>(middle);
      for (int i = 0; i < middle; i++) {
        vectorOne.add(i, vec.elementAt(i));
      }
      Vector<Double[]> vectorTwo = new Vector<Double[]>(veclength - middle);
      for (int i = middle; i < vec.size(); i++) {
        vectorTwo.add((i - middle), vec.elementAt(i));
      }
      KMeansTask taskOne = new KMeansTask(vectorOne, vector, demision, group, Threshold, numthreads);
      KMeansTask tastTwo = new KMeansTask(vectorTwo, vector, demision, group, Threshold, numthreads);
      taskOne.fork();
      tastTwo.fork();
      HashMap<Double[], Vector<Double[]>> mapOne = taskOne.join();
      HashMap<Double[], Vector<Double[]>> mapTwo = tastTwo.join();
      Iterator iter = mapOne.entrySet().iterator();
      while (iter.hasNext()) {
        Map.Entry entry = (Map.Entry) iter.next();
        Double[] key = (Double[]) entry.getKey();
        Vector<Double[]> vectorIterator = (Vector<Double[]>) entry.getValue();
        if (mapTwo.get(key) != null) {
          Vector<Double[]> temporaryVectorOne = mapTwo.get(key);
          int num = temporaryVectorOne.size();
          for (int i = 0; i < vectorIterator.size(); i++) {
            temporaryVectorOne.addElement(vectorIterator.elementAt(i + num));
          }
          mapTwo.put(key, temporaryVectorOne);
        } else {
          mapTwo.put(key, vectorIterator);
        }
      }
      return ComputerAver(mapTwo);
    }
  }

  public Vector<Double[]> getReturnVector() {
    return returnVector;
  }
}
