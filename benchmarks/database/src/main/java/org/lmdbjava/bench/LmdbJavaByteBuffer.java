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
import java.nio.ByteBuffer;
import static java.nio.ByteBuffer.allocateDirect;
import static java.nio.ByteOrder.LITTLE_ENDIAN;
import static java.nio.charset.StandardCharsets.US_ASCII;
import static org.lmdbjava.ByteBufferProxy.PROXY_OPTIMAL;
import static org.lmdbjava.ByteBufferProxy.PROXY_SAFE;
import org.lmdbjava.Cursor;
import org.lmdbjava.PutFlags;
import static org.lmdbjava.PutFlags.MDB_APPEND;
import org.lmdbjava.Txn;

public class LmdbJavaByteBuffer {

  public static class LmdbJava extends CommonLmdbJava<ByteBuffer> {

    ByteBuffer rwKey;
    ByteBuffer rwVal;

    @Override
    public void setup(File tempDir, int numEntries, final boolean sync) throws
        IOException {
      super.setup(tempDir, numEntries, sync);
      rwKey = allocateDirect(keySize).order(LITTLE_ENDIAN);
      rwVal = allocateDirect(valSize);
    }

    void write() {
      try (Txn<ByteBuffer> tx = env.txnWrite();) {
        try (Cursor<ByteBuffer> c = db.openCursor(tx);) {
          final PutFlags flags = sequential ? MDB_APPEND : null;
          final int rndByteMax = RND_MB.length - valSize;
          int rndByteOffset = 0;
          for (final int key : keys) {
            rwKey.clear();
            rwVal.clear();
            if (intKey) {
              rwKey.putInt(key).flip();
            } else {
              final byte[] str = padKey(key).getBytes(US_ASCII);
              rwKey.put(str, 0, str.length).flip();
            }
            if (valRandom) {
              rwVal.put(RND_MB, rndByteOffset, valSize).flip();
              rndByteOffset += valSize;
              if (rndByteOffset >= rndByteMax) {
                rndByteOffset = 0;
              }
            } else {
              rwVal.putInt(key);
              rwVal.position(valSize);
              rwVal.flip();
            }
            c.put(rwKey, rwVal, flags);
          }
        }
        tx.commit();
      }
    }

  }

  public static class Reader extends LmdbJava {

    Cursor<ByteBuffer> c;

    /**
     * Whether the byte buffer accessor is safe or not.
     */
    boolean forceSafe;

    Txn<ByteBuffer> txn;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      bufferProxy = forceSafe ? PROXY_SAFE : PROXY_OPTIMAL;
      super.setup(tempDir, numEntries, false);
      super.write();
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
      bufferProxy = PROXY_OPTIMAL;
      super.setup(tempDir, numEntries, sync);
    }

    @Override
    public void teardown() throws IOException {
      super.teardown();
    }
  }

}
