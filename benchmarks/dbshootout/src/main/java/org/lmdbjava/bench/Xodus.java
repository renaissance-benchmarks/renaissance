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

import java.io.IOException;
import static java.util.Arrays.copyOfRange;
import static java.util.concurrent.TimeUnit.MILLISECONDS;
import jetbrains.exodus.ArrayByteIterable;
import jetbrains.exodus.ByteIterable;
import static jetbrains.exodus.bindings.IntegerBinding.intToEntry;
import static jetbrains.exodus.bindings.StringBinding.stringToEntry;
import jetbrains.exodus.env.Cursor;
import jetbrains.exodus.env.Environment;
import jetbrains.exodus.env.EnvironmentConfig;
import static jetbrains.exodus.env.Environments.newInstance;
import jetbrains.exodus.env.Store;
import static jetbrains.exodus.env.StoreConfig.WITHOUT_DUPLICATES_WITH_PREFIXING;
import jetbrains.exodus.env.Transaction;
import static net.openhft.hashing.LongHashFunction.xx_r39;
import static org.lmdbjava.bench.Common.RND_MB;
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
public class Xodus {

  @Benchmark
  public void readCrc(final Reader r, final Blackhole bh) {
    r.crc.reset();
    try (Cursor c = r.store.openCursor(r.tx)) {
      while (c.getNext()) {
        r.crc.update(c.getKey().getBytesUnsafe(), 0, r.keySize);
        r.crc.update(c.getValue().getBytesUnsafe(), 0, r.valSize);
      }
    }
    bh.consume(r.crc.getValue());
  }

  @Benchmark
  public void readKey(final Reader r, final Blackhole bh) {
    for (final int key : r.keys) {
      if (r.intKey) {
        final ByteIterable val = r.store.get(r.tx, intToEntry(key));
        if (val != null) {
          bh.consume(val.getBytesUnsafe());
        }
      } else {
        final ByteIterable val = r.store.get(r.tx, stringToEntry(r.padKey(key)));
        if (val != null) {
          bh.consume(val.getBytesUnsafe());
        }
      }
    }
  }

  @Benchmark
  public void readRev(final Reader r, final Blackhole bh) {
    try (Cursor c = r.store.openCursor(r.tx)) {
      c.getLast();
      do {
        bh.consume(c.getValue().getBytesUnsafe());
      } while (c.getPrev());
    }
  }

  @Benchmark
  public void readSeq(final Reader r, final Blackhole bh) {
    try (Cursor c = r.store.openCursor(r.tx)) {
      while (c.getNext()) {
        bh.consume(c.getValue().getBytesUnsafe());
      }
    }
  }

  @Benchmark
  public void readXxh64(final Reader r, final Blackhole bh) {
    long result = 0;
    try (Cursor c = r.store.openCursor(r.tx)) {
      while (c.getNext()) {
        result += xx_r39().hashBytes(c.getKey().getBytesUnsafe(), 0, r.keySize);
        result += xx_r39().
            hashBytes(c.getValue().getBytesUnsafe(), 0, r.valSize);
      }
    }
    bh.consume(result);
  }

  @Benchmark
  public void write(final Writer w) {
    System.out.println("xodus");
    w.write();
  }

  @State(value = Benchmark)
  @SuppressWarnings("checkstyle:visibilitymodifier")
  public static class CommonXodus extends Common {

    Environment env;
    Store store;

    @Override
    public void setup() throws IOException {
      super.setup();

      final EnvironmentConfig cfg = new EnvironmentConfig();
      // size of immutable .xd file is 32MB
      cfg.setLogFileSize(32 * 1_024);
      cfg.setLogCachePageSize(0x2_0000);
      env = newInstance(tmp, cfg);

      env.executeInTransaction((final Transaction txn) -> {
        // WITHOUT_DUPLICATES_WITH_PREFIXING means Patricia tree is used,
        // not B+Tree (WITHOUT_DUPLICATES)
        // Patricia tree gives faster random access, both for reading and writing
        store = env.openStore("without_dups", WITHOUT_DUPLICATES_WITH_PREFIXING,
                              txn);
      });
    }

    @Override
    public void teardown() throws IOException {
      reportSpaceBeforeClose();
      env.close();
      super.teardown();
    }

    @SuppressWarnings("PMD.AvoidInstantiatingObjectsInLoops")
    void write() {
      // optimal w/ valSize=16368 + default run
      final int batchSize = Math.max(1_000_000 / valSize, 1_000);
      final RandomBytesIterator rbi = new RandomBytesIterator(valSize);
      int k = 0;
      while (k < keys.length) {
        // write in several transactions so as not to block GC
        final int keyStartIndex = k;
        k += batchSize;
        env.executeInTransaction((final Transaction tx) -> {
          for (int i = 0, j = keyStartIndex; i < batchSize && j < keys.length;
               i++, j++) {
            final int key = keys[j];
            final ByteIterable keyBi;
            final ByteIterable valBi;
            if (intKey) {
              keyBi = intToEntry(key);
            } else {
              keyBi = stringToEntry(padKey(key));
            }
            if (valRandom) {
              valBi = new ArrayByteIterable(rbi.nextBytes());
            } else {
              final byte[] bytes = new byte[valSize];
              bytes[0] = (byte) (key >>> 24);
              bytes[1] = (byte) (key >>> 16);
              bytes[2] = (byte) (key >>> 8);
              bytes[3] = (byte) key;
              valBi = new ArrayByteIterable(bytes, valSize);
            }
            if (sequential) {
              store.putRight(tx, keyBi, valBi);
            } else {
              store.put(tx, keyBi, valBi);
            }
          }
        });
      }
    }
  }

  @State(Benchmark)
  @SuppressWarnings("checkstyle:visibilitymodifier")
  public static class Reader extends CommonXodus {

    Transaction tx;

    @Setup(Trial)
    @Override
    public void setup() throws IOException {
      super.setup();
      super.write();
      tx = env.beginReadonlyTransaction();
      // cannot share Cursor, as there's no Cursor.getFirst() to reset methods
    }

    @TearDown(Trial)
    @Override
    public void teardown() throws IOException {
      tx.abort();
      super.teardown();
    }
  }

  @State(Benchmark)
  public static class Writer extends CommonXodus {

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

  private static class RandomBytesIterator {

    private int i;
    private final int rndByteMax;
    private final int valSize;

    RandomBytesIterator(final int valSize) {
      this.valSize = valSize;
      rndByteMax = RND_MB.length - valSize;
      i = 0;
    }

    byte[] nextBytes() {
      final byte[] result = copyOfRange(RND_MB, i, valSize);
      i += valSize;
      if (i >= rndByteMax) {
        i = 0;
      }
      return result;
    }
  }
}
