package io.reactors



import io.reactors.concurrent.BaselineBench
import io.reactors.concurrent.BigBench
import io.reactors.concurrent.CountingActorBench
import io.reactors.concurrent.FibonacciBench
import io.reactors.concurrent.ForkJoinCreationBench
import io.reactors.concurrent.ForkJoinThroughputBench
import io.reactors.concurrent.PingPongBench
import io.reactors.concurrent.StreamingPingPongBench
import io.reactors.concurrent.ThreadRingBench
import io.reactors.container.MatrixBench
import io.reactors.remote.RuntimeMarshalerBench
import org.scalameter.japi.JBench



class Benchmarks extends JBench.OfflineReport {
  attach(new BaselineBench)
  attach(new PingPongBench)
  attach(new StreamingPingPongBench)
  attach(new ThreadRingBench)
  attach(new CountingActorBench)
  attach(new ForkJoinCreationBench)
  attach(new ForkJoinThroughputBench)
  attach(new FibonacciBench)
  attach(new BigBench)
  attach(new MatrixBench)
  attach(new RuntimeMarshalerBench)
}
