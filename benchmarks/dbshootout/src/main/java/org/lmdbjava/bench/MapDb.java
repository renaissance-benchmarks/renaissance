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
import java.util.Iterator;
import java.util.Map.Entry;
import static java.util.concurrent.TimeUnit.MILLISECONDS;
import static net.openhft.hashing.LongHashFunction.xx_r39;
import org.agrona.MutableDirectBuffer;
import org.agrona.concurrent.UnsafeBuffer;
import org.mapdb.BTreeMap;
import org.mapdb.DB;
import static org.mapdb.DBMaker.fileDB;
import static org.mapdb.Serializer.BYTE_ARRAY;
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
public class MapDb {

  @Benchmark
  public void readCrc(final Reader r, final Blackhole bh) {
    r.crc.reset();
    final Iterator<Entry<byte[], byte[]>> iterator = r.map.entryIterator();
    while (iterator.hasNext()) {
      final Entry<byte[], byte[]> entry = iterator.next();
      r.crc.update(entry.getKey());
      r.crc.update(entry.getValue());
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
      out = r.map.get(r.wkb.byteArray());
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
            if (r.map.get(localwkb.byteArray()) == null) {
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
    final Iterator<Entry<byte[], byte[]>> iterator = r.map
        .descendingEntryIterator();
    while (iterator.hasNext()) {
      final Entry<byte[], byte[]> entry = iterator.next();
      bh.consume(entry.getValue());
    }
  }

  @Benchmark
  public void readSeq(final Reader r, final Blackhole bh) {
    final Iterator<Entry<byte[], byte[]>> iterator = r.map.entryIterator();
    while (iterator.hasNext()) {
      final Entry<byte[], byte[]> entry = iterator.next();
      bh.consume(entry.getValue());
    }
  }

  @Benchmark
  public void readXxh64(final Reader r, final Blackhole bh) {
    long result = 0;
    final Iterator<Entry<byte[], byte[]>> iterator = r.map.entryIterator();
    while (iterator.hasNext()) {
      final Entry<byte[], byte[]> entry = iterator.next();
      result += xx_r39().hashBytes(entry.getKey());
      result += xx_r39().hashBytes(entry.getValue());
    }
    bh.consume(result);
  }

  @Benchmark
  public void write(final Writer w) {
    w.write();
  }

  @Benchmark
  public void parWrite(final Writer w) {
    w.parWrite();
  }

  @State(value = Benchmark)
  @SuppressWarnings("checkstyle:visibilitymodifier")
  public static class CommonMapDb extends Common {

    DB db;
    BTreeMap<byte[], byte[]> map;

    /**
     * Writable key buffer. Backed by a plain byte[] for MapDb API ease.
     */
    MutableDirectBuffer wkb;

    /**
     * Writable value buffer. Backed by a plain byte[] for MapDb API ease.
     */
    MutableDirectBuffer wvb;

    @Override
    public void setup() throws IOException {
      super.setup();
      wkb = new UnsafeBuffer(new byte[keySize]);
      wvb = new UnsafeBuffer(new byte[valSize]);
      db = fileDB(new File(tmp, "map.db"))
          .fileMmapEnable()
          // .concurrencyDisable()
          .allocateStartSize(num * valSize)
          .make();
      map = db.treeMap("ba2ba")
          .keySerializer(BYTE_ARRAY)
          .valueSerializer(BYTE_ARRAY)
          .createOrOpen();
    }

    @Override
    public void teardown() throws IOException {
      reportSpaceBeforeClose();
      db.close();
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
        map.put(wkb.byteArray(), wvb.byteArray());
      }
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
              map.put(localwkb.byteArray(), localwvb.byteArray());
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
  }

  @State(Benchmark)
  public static class Reader extends CommonMapDb {
    public void setNum(Integer x) {
      num = x;
    }

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
  public static class Writer extends CommonMapDb {
    public void setNum(Integer x) {
      num = x;
    }

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
