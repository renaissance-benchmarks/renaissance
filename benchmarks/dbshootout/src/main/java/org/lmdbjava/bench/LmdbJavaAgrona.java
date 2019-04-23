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
import static java.lang.Boolean.TRUE;
import static java.lang.System.setProperty;
import static java.nio.ByteBuffer.allocateDirect;
import static java.nio.ByteOrder.LITTLE_ENDIAN;
import static java.util.concurrent.TimeUnit.MILLISECONDS;
import static net.openhft.hashing.LongHashFunction.xx_r39;
import org.agrona.DirectBuffer;
import org.agrona.MutableDirectBuffer;
import org.agrona.concurrent.UnsafeBuffer;
import static org.agrona.concurrent.UnsafeBuffer.DISABLE_BOUNDS_CHECKS_PROP_NAME;
import static org.lmdbjava.CopyFlags.MDB_CP_COMPACT;
import org.lmdbjava.Cursor;
import static org.lmdbjava.DirectBufferProxy.PROXY_DB;
import static org.lmdbjava.GetOp.MDB_SET_KEY;
import org.lmdbjava.PutFlags;
import static org.lmdbjava.PutFlags.MDB_APPEND;
import static org.lmdbjava.SeekOp.MDB_FIRST;
import static org.lmdbjava.SeekOp.MDB_LAST;
import static org.lmdbjava.SeekOp.MDB_NEXT;
import static org.lmdbjava.SeekOp.MDB_PREV;
import org.lmdbjava.Txn;
import org.openjdk.jmh.annotations.Benchmark;
import org.openjdk.jmh.annotations.BenchmarkMode;
import org.openjdk.jmh.annotations.Fork;
import static org.openjdk.jmh.annotations.Level.Invocation;
import static org.openjdk.jmh.annotations.Level.Trial;
import org.openjdk.jmh.annotations.Measurement;
import static org.openjdk.jmh.annotations.Mode.SampleTime;
import org.openjdk.jmh.annotations.OutputTimeUnit;
import org.openjdk.jmh.annotations.Param;
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
public class LmdbJavaAgrona {

  @Benchmark
  public void readCrc(final Reader r, final Blackhole bh) {
    r.crc.reset();
    bh.consume(r.c.seek(MDB_FIRST));
    do {
      r.txn.key().getBytes(0, r.keyBytes, 0, r.keySize);
      r.txn.val().getBytes(0, r.valBytes, 0, r.valSize);
      r.crc.update(r.keyBytes);
      r.crc.update(r.valBytes);
    } while (r.c.seek(MDB_NEXT));
    bh.consume(r.crc.getValue());
  }

  @Benchmark
  public void readKey(final Reader r, final Blackhole bh) {
    for (final int key : r.keys) {
      if (r.intKey) {
        r.rwKey.putInt(0, key);
      } else {
        r.rwKey.putStringWithoutLengthUtf8(0, r.padKey(key));
      }
      bh.consume(r.c.get(r.rwKey, MDB_SET_KEY));
      bh.consume(r.txn.val());
    }
  }

  @Benchmark
  public void readRev(final Reader r, final Blackhole bh) {
    bh.consume(r.c.seek(MDB_LAST));
    do {
      bh.consume(r.txn.val());
    } while (r.c.seek(MDB_PREV));
  }

  @Benchmark
  public void readSeq(final Reader r, final Blackhole bh) {
    bh.consume(r.c.seek(MDB_FIRST));
    do {
      bh.consume(r.txn.val());
    } while (r.c.seek(MDB_NEXT));
  }

  @Benchmark
  public void readXxh64(final Reader r, final Blackhole bh) {
    long result = 0;
    bh.consume(r.c.seek(MDB_FIRST));
    do {
      result += xx_r39().hashMemory(r.txn.key().addressOffset(), r.keySize);
      result += xx_r39().hashMemory(r.txn.val().addressOffset(), r.valSize);
    } while (r.c.seek(MDB_NEXT));
    bh.consume(result);
  }

  @Benchmark
  public void write(final Writer w) {
    System.out.println("lmdb-agrona");
    w.write();
  }

  @State(Benchmark)
  @SuppressWarnings("checkstyle:visibilitymodifier")
  public static class LmdbJava extends CommonLmdbJava<DirectBuffer> {

    /**
     * CRC scratch (memory-mapped MDB can't return a byte[] or ByteBuffer).
     */
    byte[] keyBytes;

    MutableDirectBuffer rwKey;
    MutableDirectBuffer rwVal;
    /**
     * CRC scratch (memory-mapped MDB can't return a byte[] or ByteBuffer).
     */
    byte[] valBytes;

    static {
      setProperty(DISABLE_BOUNDS_CHECKS_PROP_NAME, TRUE.toString());
    }

    @Override
    public void setup(final boolean sync) throws
        IOException {
      super.setup(sync);
      keyBytes = new byte[keySize];
      valBytes = new byte[valSize];
      rwKey = new UnsafeBuffer(allocateDirect(keySize).order(LITTLE_ENDIAN));
      rwVal = new UnsafeBuffer(allocateDirect(valSize));
    }

    void write() {
      try (Txn<DirectBuffer> tx = env.txnWrite()) {
        try (Cursor<DirectBuffer> c = db.openCursor(tx);) {
          final PutFlags flags = sequential ? MDB_APPEND : null;
          final int rndByteMax = RND_MB.length - valSize;
          int rndByteOffset = 0;
          for (final int key : keys) {
            if (intKey) {
              rwKey.putInt(0, key);
            } else {
              rwKey.putStringWithoutLengthUtf8(0, padKey(key));
            }
            if (valRandom) {
              rwVal.putBytes(0, RND_MB, rndByteOffset, valSize);
              rndByteOffset += valSize;
              if (rndByteOffset >= rndByteMax) {
                rndByteOffset = 0;
              }
            } else {
              rwVal.putInt(0, key);
            }
            c.put(rwKey, rwVal, flags);
          }
        }
        tx.commit();
      }
    }

  }

  @State(Benchmark)
  @SuppressWarnings("checkstyle:visibilitymodifier")
  public static class Reader extends LmdbJava {

    Cursor<DirectBuffer> c;
    Txn<DirectBuffer> txn;

    @Setup(Trial)
    @Override
    public void setup() throws IOException {
      bufferProxy = PROXY_DB;
      super.setup(false);
      super.write();
      final int maxValSizeForCopy = 4_081; // 2nd copy requires *2 /tmp space
      if (valSize <= maxValSizeForCopy && tmp.getName().contains(".readKey-")) {
        env.copy(compact, MDB_CP_COMPACT);
        reportSpaceUsed(compact, "compacted");
      }
      txn = env.txnRead();
      c = db.openCursor(txn);
    }

    @TearDown(Trial)
    @Override
    public void teardown() throws IOException {
      c.close();
      txn.abort();
      super.teardown();
    }
  }

  @State(Benchmark)
  @SuppressWarnings("checkstyle:visibilitymodifier")
  public static class Writer extends LmdbJava {

    /**
     * Whether <code>MDB_NOSYNC</code> is used.
     */
    @Param("false")
    boolean sync;

    @Setup(Invocation)
    @Override
    public void setup() throws IOException {
      bufferProxy = PROXY_DB;
      super.setup(sync);
    }

    @TearDown(Invocation)
    @Override
    public void teardown() throws IOException {
      super.teardown();
    }
  }

}
