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
import org.lmdbjava.PutFlags;
import static org.lmdbjava.PutFlags.MDB_APPEND;
import org.lmdbjava.Txn;

public class LmdbJavaAgrona {

  public void write(final Writer w) {
    System.out.println("lmdb-agrona");
    w.write();
  }

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
    public void setup(File tempDir, int numEntries, final boolean sync) throws
        IOException {
      super.setup(tempDir, numEntries, sync);
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

  public static class Reader extends LmdbJava {

    Cursor<DirectBuffer> c;
    Txn<DirectBuffer> txn;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      bufferProxy = PROXY_DB;
      super.setup(tempDir, numEntries, false);
      super.write();
      final int maxValSizeForCopy = 4_081; // 2nd copy requires *2 /tmp space
      if (valSize <= maxValSizeForCopy && tmp.getName().contains(".readKey-")) {
        env.copy(compact, MDB_CP_COMPACT);
        reportSpaceUsed(compact, "compacted");
      }
      txn = env.txnRead();
      c = db.openCursor(txn);
    }

    @Override
    public void teardown() throws IOException {
      c.close();
      txn.abort();
      super.teardown();
    }
  }

  public static class Writer extends LmdbJava {

    /**
     * Whether <code>MDB_NOSYNC</code> is used.
     */
    boolean sync;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      bufferProxy = PROXY_DB;
      super.setup(tempDir, numEntries, sync);
    }

    @Override
    public void teardown() throws IOException {
      super.teardown();
    }
  }

}
