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
import static org.rocksdb.CompressionType.NO_COMPRESSION;
import org.rocksdb.Options;
import org.rocksdb.RocksDB;
import static org.rocksdb.RocksDB.loadLibrary;
import static org.rocksdb.RocksDB.open;
import org.rocksdb.RocksDBException;
import org.rocksdb.WriteBatch;
import org.rocksdb.WriteOptions;

public class RocksDb {

  public static class CommonRocksDb extends Common {

    RocksDB db;

    /**
     * Writable key buffer. Backed by a plain byte[] for RocksDB API ease.
     */
    MutableDirectBuffer wkb;

    /**
     * Writable value buffer. Backed by a plain byte[] for RocksDB API ease.
     */
    MutableDirectBuffer wvb;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries);
      wkb = new UnsafeBuffer(new byte[keySize]);
      wvb = new UnsafeBuffer(new byte[valSize]);
      loadLibrary();
      final Options options = new Options();
      options.setCreateIfMissing(true);
      options.setCompressionType(NO_COMPRESSION);
      try {
        db = open(options, tmp.getAbsolutePath());
      } catch (final RocksDBException ex) {
        throw new IOException(ex);
      }
    }

    @Override
    public void teardown() throws IOException {
      reportSpaceBeforeClose();
      if (db != null) {
        db.close();
      }
      super.teardown();
    }

    void write(final int batchSize) throws IOException {
      final int rndByteMax = RND_MB.length - valSize;
      int rndByteOffset = 0;

      final WriteBatch batch = new WriteBatch();
      final WriteOptions opt = new WriteOptions();
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
          try {
            db.write(opt, batch);
          } catch (final RocksDBException ex) {
            throw new IOException(ex);
          }
          batch.clear();
        }
      }
      try {
        db.write(opt, batch); // possible partial batch
      } catch (final RocksDBException ex) {
        throw new IOException(ex);
      }
      batch.clear();
    }
  }

  public static class Reader extends CommonRocksDb {

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

  public static class Writer extends CommonRocksDb {

    int batchSize;

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
