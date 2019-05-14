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
import net.openhft.chronicle.map.ChronicleMap;
import static net.openhft.chronicle.map.ChronicleMap.of;
import org.agrona.MutableDirectBuffer;
import org.agrona.concurrent.UnsafeBuffer;

public class Chronicle {

  // TODO: Consolidate benchmark parameters across the suite.
  //  See: https://github.com/renaissance-benchmarks/renaissance/issues/27
  final static int CPU = Runtime.getRuntime().availableProcessors();

  private static volatile Object out = null;

  // Chronicle Map does not provide ordered keys, so no CRC/XXH64/rev/prev test
  public void readKey(final Reader r) {
    for (final int key : r.keys) {
      if (r.intKey) {
        r.wkb.putInt(0, key);
      } else {
        r.wkb.putStringWithoutLengthUtf8(0, r.padKey(key));
      }
      out = r.map.getUsing(r.wkb.byteArray(), r.wvb.byteArray());
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
            r.map.getUsing(localwkb.byteArray(), localwvb.byteArray());
            if (localwvb.getInt(0) == 0) {
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

  public void write(final Writer w) {
    w.write();
  }

  public void parWrite(final Writer w) {
    w.parWrite();
  }

  public static class CommonChronicleMap extends Common {

    ChronicleMap<byte[], byte[]> map;

    /**
     * Writable key buffer. Backed by a plain byte[] for Chronicle API ease.
     */
    MutableDirectBuffer wkb;

    /**
     * Writable value buffer. Backed by a plain byte[] for Chronicle API ease.
     */
    MutableDirectBuffer wvb;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries);
      wkb = new UnsafeBuffer(new byte[keySize]);
      wvb = new UnsafeBuffer(new byte[valSize]);

      try {
        File chronicleMapFile = new File(tmp, "chronicle.map");
        map = of(byte[].class, byte[].class)
            .constantKeySizeBySample(new byte[keySize])
            .constantValueSizeBySample(new byte[valSize])
            .entries(num)
            .createPersistedTo(chronicleMapFile);
      } catch (final IOException ex) {
        throw new IllegalStateException(ex);
      }
    }

    @Override
    public void teardown() throws IOException {
      reportSpaceBeforeClose();
      map.close();
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

  public static class Reader extends CommonChronicleMap {

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries);
      super.write();
    }

    @Override
    public void teardown() throws IOException {
      super.teardown();
    }
  }

  public static class Writer extends CommonChronicleMap {

    @Override
    public final void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries);
    }

    @Override
    public final void teardown() throws IOException {
      super.teardown();
    }
  }

}
