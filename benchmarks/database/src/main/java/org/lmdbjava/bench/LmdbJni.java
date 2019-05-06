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
import org.fusesource.lmdbjni.BufferCursor;
import org.fusesource.lmdbjni.Database;
import org.fusesource.lmdbjni.DirectBuffer;
import static org.fusesource.lmdbjni.DirectBuffer.DISABLE_BOUNDS_CHECKS_PROP_NAME;
import org.fusesource.lmdbjni.Env;
import org.fusesource.lmdbjni.Transaction;
import org.lmdbjava.DbiFlags;
import org.lmdbjava.EnvFlags;
import static org.lmdbjava.MaskedFlag.mask;
import static org.lmdbjava.bench.CommonLmdbJava.POSIX_MODE;
import static org.lmdbjava.bench.CommonLmdbJava.dbiFlags;
import static org.lmdbjava.bench.CommonLmdbJava.envFlags;
import static org.lmdbjava.bench.CommonLmdbJava.mapSize;

public class LmdbJni {

  public static class CommonLmdbJni extends Common {

    Database db;
    Env env;

    /**
     * CRC scratch (memory-mapped MDB can't return a byte[] or ByteBuffer).
     */
    byte[] keyBytes;

    /**
     * CRC scratch (memory-mapped MDB can't return a byte[] or ByteBuffer).
     */
    byte[] valBytes;

    /**
     * CRC scratch (memory-mapped MDB can't return a byte[] or ByteBuffer).
     */
    DirectBuffer wkb;

    /**
     * Whether {@link EnvFlags#MDB_WRITEMAP} is used.
     */
    boolean writeMap;

    /**
     * Writable value buffer.
     */
    DirectBuffer wvb;

    static {
      setProperty(DISABLE_BOUNDS_CHECKS_PROP_NAME, TRUE.toString());
    }

    public void setup(File tempDir, int numEntries, final boolean sync) throws
        IOException {
      super.setup(tempDir, numEntries);
      wkb = new DirectBuffer(allocateDirect(keySize));
      wvb = new DirectBuffer(allocateDirect(valSize));
      keyBytes = new byte[keySize];
      valBytes = new byte[valSize];

      final EnvFlags[] envFlags = envFlags(writeMap, sync);

      env = new Env();
      env.setMapSize(mapSize(num, valSize));
      env.setMaxDbs(1);
      env.setMaxReaders(2);
      env.open(tmp.getAbsolutePath(), mask(envFlags), POSIX_MODE);

      try (Transaction tx = env.createWriteTransaction()) {
        final DbiFlags[] flags = dbiFlags(intKey);
        db = env.openDatabase(tx, "db", mask(flags));
        tx.commit();
      }
    }

    @Override
    public void teardown() throws IOException {
      reportSpaceBeforeClose();
      env.close();
      super.teardown();
    }

    void write() {
      try (Transaction tx = env.createWriteTransaction()) {
        try (BufferCursor c = db.bufferCursor(tx);) {
          final int rndByteMax = RND_MB.length - valSize;
          int rndByteOffset = 0;
          for (final int key : keys) {
            if (intKey) {
              wkb.putInt(0, key);
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
            c.keyWrite(wkb);
            c.valWrite(wvb);
            if (sequential) {
              c.append();
            } else {
              c.overwrite();
            }
          }
        }
        tx.commit();
      }
    }
  }

  public static class Reader extends CommonLmdbJni {

    BufferCursor c;
    Transaction tx;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries, false);
      super.write();
      tx = env.createReadTransaction();
      c = db.bufferCursor(tx);
    }

    @Override
    public void teardown() throws IOException {
      c.close();
      tx.abort();
      super.teardown();
    }
  }

  public static class Writer extends CommonLmdbJni {

    /**
     * Whether {@link EnvFlags#MDB_NOSYNC} is used.
     */
    boolean sync;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries, sync);
    }

    @Override
    public void teardown() throws IOException {
      super.teardown();
    }
  }

}
