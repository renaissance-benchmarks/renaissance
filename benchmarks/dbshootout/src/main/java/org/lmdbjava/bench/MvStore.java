/*-
 * #%L
 * LmdbJava Benchmarks
 * %%
 * Copyright (C) 2016 - 2018 The LmdbJava Open Source Project
 * %%
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 * 
 *      http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * #L%
 */

package org.lmdbjava.bench;

import java.io.File;
import java.io.IOException;
import static java.nio.ByteOrder.LITTLE_ENDIAN;
import static java.util.Arrays.copyOf;
import java.util.Iterator;
import static java.util.concurrent.TimeUnit.MILLISECONDS;
import static net.openhft.hashing.LongHashFunction.xx_r39;
import org.agrona.MutableDirectBuffer;
import org.agrona.concurrent.UnsafeBuffer;
import org.h2.mvstore.MVMap;
import org.h2.mvstore.MVStore;
import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Fork;
import static org.openjdk.jmh.annotations.Level.Invocation;
import static org.openjdk.jmh.annotations.Level.Trial;
import org.openjdk.jmh.annotations.Measurement;
import static org.openjdk.jmh.annotations.Mode.SampleTime;
import org.openjdk.jmh.annotations.OutputTimeUnit;
import static org.openjdk.jmh.annotations.Scope.Benchmark;
import org.openjdk.jmh.annotations.Setup;
import org.openjdk.jmh.annotations.State;
import org.openjdk.jmh.annotations.TearDown;
import org.openjdk.jmh.annotations.Warmup;
import org.openjdk.jmh.infra.Blackhole;

@OutputTimeUnit(MILLISECONDS)
@Fork(1)
@Warmup(iterations = 3)
@Measurement(iterations = 3)
@BenchmarkMode(SampleTime)
@SuppressWarnings({"checkstyle:javadoctype", "checkstyle:designforextension"})
public class MvStore {

  @Benchmark
  public void readCrc(final Reader r, final Blackhole bh) {
    r.crc.reset();
    final Iterator<byte[]> iter = r.map.keyIterator(null);
    while (iter.hasNext()) {
      final byte[] k = iter.next();
      final byte[] v = r.map.get(k);
      r.crc.update(k);
      r.crc.update(v);
    }
    bh.consume(r.crc.getValue());
  }

  private static volatile Object out = null;

  @Benchmark
  public void readKey(final Reader r) {
    for (final int key : r.keys) {
      if (r.intKey) {
        r.wkb.putInt(0, key);
      } else {
        r.wkb.putStringWithoutLengthUtf8(0, r.padKey(key));
      }
      out = r.map.get(copyOf(r.wkb.byteArray(), r.keySize));
    }
  }

  @Benchmark
  public void parReadKey(final Reader r) {
    final int CPU = Runtime.getRuntime().availableProcessors();
    final int[] keys = r.keys;
    Thread[] threads = new Thread[CPU];
    for (int k = 0; k < CPU; k++) {
      final int p = k;
      final int BATCH = keys.length / CPU;
      threads[p] = new Thread() {
        public void run() {
          MutableDirectBuffer localwkb = new UnsafeBuffer(new byte[r.keySize]);
          MutableDirectBuffer localwvb = new UnsafeBuffer(new byte[r.valSize]);
          final int rndByteMax = r.RND_MB.length - r.valSize;
          int rndByteOffset = 0;
          for (int i = p * BATCH; i < p * BATCH + BATCH; i++) {
            int key = keys[i];
            if (r.intKey) {
              localwkb.putInt(0, key);
            } else {
              localwkb.putStringWithoutLengthUtf8(0, r.padKey(key));
            }
            if (r.map.get(copyOf(localwkb.byteArray(), r.keySize)) == null) {
              out = localwkb;
            }
          }
        }
      };
      threads[p].start();
    }
    for (int p = 0; p < CPU; p++) {
      try {
        threads[p].join();
      } catch (Exception e) {
        throw new RuntimeException(e);
      }
    }
  }

  @Benchmark
  public void readRev(final Reader r, final Blackhole bh) {
    for (long i = r.map.sizeAsLong() - 1; i >= 0; i--) {
      final byte[] k = r.map.getKey(i);
      bh.consume(r.map.get(k));
    }
  }

  @Benchmark
  public void readSeq(final Reader r, final Blackhole bh) {
    final Iterator<byte[]> iter = r.map.keyIterator(null);
    while (iter.hasNext()) {
      final byte[] k = iter.next();
      bh.consume(r.map.get(k));
    }
  }

  @Benchmark
  public void readXxh64(final Reader r, final Blackhole bh) {
    long result = 0;
    final Iterator<byte[]> iter = r.map.keyIterator(null);
    while (iter.hasNext()) {
      final byte[] k = iter.next();
      final byte[] v = r.map.get(k);
      result += xx_r39().hashBytes(k);
      result += xx_r39().hashBytes(v);
    }
    bh.consume(result);
  }

  @Benchmark
  public void parWrite(final Writer w) {
    w.parWrite();
  }

  @Benchmark
  public void write(final Writer w) {
    w.write();
  }

  @State(value = Benchmark)
  @SuppressWarnings("checkstyle:visibilitymodifier")
  public static class CommonMvStore extends Common {

    MVMap<byte[], byte[]> map;
    MVStore s;

    /**
     * Writable key buffer. Backed by a plain byte[] for MvStore API ease.
     */
    MutableDirectBuffer wkb;

    /**
     * Writable value buffer. Backed by a plain byte[] for MvStore API ease.
     */
    MutableDirectBuffer wvb;

    @Override
    public void setup() throws IOException {
      super.setup();
      wkb = new UnsafeBuffer(new byte[keySize]);
      wvb = new UnsafeBuffer(new byte[valSize]);
      s = new MVStore.Builder()
          .fileName(new File(tmp, "mvstore.db").getAbsolutePath())
          .autoCommitDisabled()
          .open();
      map = s.openMap("ba2ba");
    }

    @Override
    public void teardown() throws IOException {
      reportSpaceBeforeClose();
      s.close();
      super.teardown();
    }

    void write() {
      final int rndByteMax = RND_MB.length - valSize;
      int rndByteOffset = 0;
      for (final int key : keys) {
        if (intKey) {
          wkb.putInt(0, key, LITTLE_ENDIAN);
        } else {
          wkb.putStringWithoutLengthUtf8(0, padKey(key));
        }
        if (valRandom) {
          wvb.putBytes(0, RND_MB, rndByteOffset, valSize);
          rndByteOffset += valSize;
          if (rndByteOffset >= rndByteMax) {
            rndByteOffset = 0;
          }
        } else {
          wvb.putInt(0, key);
        }
        // MvStore requires this copy, otherwise it never stores > 1 entry
        map.put(copyOf(wkb.byteArray(), keySize),
                copyOf(wvb.byteArray(), valSize));
      }
      s.commit();
    }

    void parWrite() {
      final int CPU = Runtime.getRuntime().availableProcessors();
      Thread[] threads = new Thread[CPU];
      for (int k = 0; k < CPU; k++) {
        final int p = k;
        final int BATCH = keys.length / CPU;
        threads[p] = new Thread() {
          public void run() {
            MutableDirectBuffer localwkb = new UnsafeBuffer(new byte[keySize]);
            MutableDirectBuffer localwvb = new UnsafeBuffer(new byte[valSize]);
            final int rndByteMax = RND_MB.length - valSize;
            int rndByteOffset = 0;
            for (int i = p * BATCH; i < p * BATCH + BATCH; i++) {
              // if (i % 1000 == 0) {
              //   System.out.println("thread " + p + ", key " + i);
              // }
              int key = keys[i];
              if (intKey) {
                localwkb.putInt(0, key, LITTLE_ENDIAN);
              } else {
                localwkb.putStringWithoutLengthUtf8(0, padKey(key));
              }
              if (valRandom) {
                localwvb.putBytes(0, RND_MB, rndByteOffset, valSize);
                rndByteOffset += valSize;
                if (rndByteOffset >= rndByteMax) {
                  rndByteOffset = 0;
                }
              } else {
                localwvb.putInt(0, key);
              }
              map.put(copyOf(localwkb.byteArray(), keySize),
                copyOf(localwvb.byteArray(), valSize));
            }
            s.commit();
          }
        };
        threads[p].start();
      }
      for (int p = 0; p < CPU; p++) {
        try {
          threads[p].join();
        } catch (Exception e) {
          throw new RuntimeException(e);
        }
      }
    }
  }

  @State(Benchmark)
  public static class Reader extends CommonMvStore {

    @Setup(Trial)
    @Override
    public void setup() throws IOException {
      super.setup();
      super.write();
    }

    @TearDown(Trial)
    @Override
    public void teardown() throws IOException {
      super.teardown();
    }
  }

  @State(Benchmark)
  public static class Writer extends CommonMvStore {

    @Setup(Invocation)
    @Override
    public void setup() throws IOException {
      super.setup();
    }

    @TearDown(Invocation)
    @Override
    public void teardown() throws IOException {
      super.teardown();
    }
  }

}
