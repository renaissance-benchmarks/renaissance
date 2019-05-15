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
import org.agrona.MutableDirectBuffer;
import org.agrona.concurrent.UnsafeBuffer;
import static org.fusesource.leveldbjni.JniDBFactory.factory;
import static org.fusesource.leveldbjni.JniDBFactory.popMemoryPool;
import static org.fusesource.leveldbjni.JniDBFactory.pushMemoryPool;
import static org.iq80.leveldb.CompressionType.NONE;
import org.iq80.leveldb.DB;
import org.iq80.leveldb.Options;
import org.iq80.leveldb.WriteBatch;

public class LevelDb {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27
  final static int CPU = Runtime.getRuntime().availableProcessors();

  private static volatile Object out = null;

  public void readKey(final Reader r) throws IOException {
    for (final int key : r.keys) {
      if (r.intKey) {
        r.wkb.putInt(0, key);
      } else {
        r.wkb.putStringWithoutLengthUtf8(0, r.padKey(key));
      }
      out = r.db.get(r.wkb.byteArray());
    }
  }

  public void parReadKey(final Reader r) {
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
            if (r.db.get(localwkb.byteArray()) == null) {
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

  public void write(final Writer w) throws IOException {
    w.write(w.batchSize);
  }

  public void parWrite(final Writer w) throws IOException {
    w.parWrite(w.batchSize);
  }

  public static class CommonLevelDb extends Common {

    DB db;

    /**
     * Writable key buffer. Backed by a plain byte[] for LevelDB API ease.
     */
    MutableDirectBuffer wkb;

    /**
     * Writable value buffer. Backed by a plain byte[] for LevelDB API ease.
     */
    MutableDirectBuffer wvb;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries);
      wkb = new UnsafeBuffer(new byte[keySize]);
      wvb = new UnsafeBuffer(new byte[valSize]);
      pushMemoryPool(1_024 * 512);
      final Options options = new Options();
      options.createIfMissing(true);
      options.compressionType(NONE);
      db = factory.open(tmp, options);
    }

    @Override
    public void teardown() throws IOException {
      reportSpaceBeforeClose();
      db.close();
      popMemoryPool();
      super.teardown();
    }

    void write(final int batchSize) throws IOException {
      final int rndByteMax = RND_MB.length - valSize;
      int rndByteOffset = 0;
      WriteBatch batch = db.createWriteBatch();
      for (int i = 0; i < keys.length; i++) {
        final int key = keys[i];
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
        batch.put(wkb.byteArray(), wvb.byteArray());
        if (i % batchSize == 0) {
          db.write(batch);
          batch.close();
          batch = db.createWriteBatch();
        }
      }
      db.write(batch); // possible partial batch
      batch.close();
    }

    void parWrite(final int batchSize) {
      Thread[] threads = new Thread[CPU];
      for (int k = 0; k < CPU; k++) {
        final int p = k;
        final int BATCH = keys.length / CPU;
        threads[p] = new Thread() {
          public void run() {
            try {
              doIt();
            } catch (Exception e) {
              throw new RuntimeException(e);
            }
          }

          public void doIt() throws IOException {
            WriteBatch batch = db.createWriteBatch();
            MutableDirectBuffer localwkb = new UnsafeBuffer(new byte[keySize]);
            MutableDirectBuffer localwvb = new UnsafeBuffer(new byte[valSize]);
            final int rndByteMax = RND_MB.length - valSize;
            int rndByteOffset = 0;
            for (int i = p * BATCH; i < p * BATCH + BATCH; i++) {
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
              batch.put(localwkb.byteArray(), localwvb.byteArray());
              if (i % batchSize == 0) {
                db.write(batch);
                batch.close();
                batch = db.createWriteBatch();
              }
            }
            db.write(batch);
            batch.close();
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

  public static class Reader extends CommonLevelDb {

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries);
      super.write(num);
    }

    @Override
    public void teardown() throws IOException {
      super.teardown();
    }
  }

  public static class Writer extends CommonLevelDb {

    int batchSize = 250000;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries);
    }

    @Override
    public void teardown() throws IOException {
      super.teardown();
    }
  }

}
