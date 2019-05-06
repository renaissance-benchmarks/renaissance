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
import java.nio.IntBuffer;
import org.lwjgl.PointerBuffer;
import org.lwjgl.system.MemoryStack;
import static org.lwjgl.system.MemoryStack.stackPush;
import static org.lwjgl.system.MemoryUtil.NULL;
import static org.lwjgl.util.lmdb.LMDB.MDB_APPEND;
import static org.lwjgl.util.lmdb.LMDB.MDB_CREATE;
import static org.lwjgl.util.lmdb.LMDB.MDB_INTEGERKEY;
import static org.lwjgl.util.lmdb.LMDB.MDB_NOSYNC;
import static org.lwjgl.util.lmdb.LMDB.MDB_RDONLY;
import static org.lwjgl.util.lmdb.LMDB.MDB_SUCCESS;
import static org.lwjgl.util.lmdb.LMDB.MDB_WRITEMAP;
import static org.lwjgl.util.lmdb.LMDB.mdb_cursor_close;
import static org.lwjgl.util.lmdb.LMDB.mdb_cursor_open;
import static org.lwjgl.util.lmdb.LMDB.mdb_cursor_put;
import static org.lwjgl.util.lmdb.LMDB.mdb_dbi_open;
import static org.lwjgl.util.lmdb.LMDB.mdb_env_close;
import static org.lwjgl.util.lmdb.LMDB.mdb_env_create;
import static org.lwjgl.util.lmdb.LMDB.mdb_env_open;
import static org.lwjgl.util.lmdb.LMDB.mdb_env_set_mapsize;
import static org.lwjgl.util.lmdb.LMDB.mdb_env_set_maxdbs;
import static org.lwjgl.util.lmdb.LMDB.mdb_env_set_maxreaders;
import static org.lwjgl.util.lmdb.LMDB.mdb_strerror;
import static org.lwjgl.util.lmdb.LMDB.mdb_txn_abort;
import static org.lwjgl.util.lmdb.LMDB.mdb_txn_begin;
import static org.lwjgl.util.lmdb.LMDB.mdb_txn_commit;
import org.lwjgl.util.lmdb.MDBVal;
import static org.lwjgl.util.lmdb.MDBVal.mallocStack;

public class LmdbLwjgl {

  public static class CommonLmdbLwjgl extends Common {

    private static final int POSIX_MODE = 664;

    int db;
    long env;

    /**
     * Whether <code>MDB_WRITEMAP</code> is used.
     */
    boolean writeMap;

    static void E(final int rc) {
      if (rc != MDB_SUCCESS) {
        throw new IllegalStateException(mdb_strerror(rc));
      }
    }

    private static int dbiFlags(final boolean intKey) {
      final int flags;
      if (intKey) {
        flags = MDB_CREATE | MDB_INTEGERKEY;
      } else {
        flags = MDB_CREATE;
      }
      return flags;
    }

    private static int envFlags(final boolean writeMap, final boolean sync) {
      int envFlags = 0;
      if (writeMap) {
        envFlags |= MDB_WRITEMAP;
      }
      if (!sync) {
        envFlags |= MDB_NOSYNC;
      }
      return envFlags;
    }

    private static long mapSize(final int num, final int valSize) {
      return num * ((long) valSize) * 32L / 10L;
    }

    public void setup(File tempDir, int numEntries, final boolean sync) throws
        IOException {
      super.setup(tempDir, numEntries);

      try (MemoryStack stack = stackPush()) {
        final PointerBuffer pp = stack.mallocPointer(1);

        E(mdb_env_create(pp));
        env = pp.get(0);

        E(mdb_env_set_maxdbs(env, 1));
        E(mdb_env_set_maxreaders(env, 2));
        E(mdb_env_set_mapsize(env, mapSize(num, valSize)));

        // Open environment
        E(mdb_env_open(env, tmp.getPath(), envFlags(writeMap, sync), POSIX_MODE));

        // Open database
        E(mdb_txn_begin(env, NULL, 0, pp));
        final long txn = pp.get(0);

        final IntBuffer ip = stack.mallocInt(1);
        E(mdb_dbi_open(txn, "db", dbiFlags(intKey), ip));
        db = ip.get(0);

        mdb_txn_commit(txn);
      }
    }

    @Override
    public void teardown() throws IOException {
      reportSpaceBeforeClose();
      mdb_env_close(env);
      super.teardown();
    }

    void write() {
      try (MemoryStack stack = stackPush()) {
        final PointerBuffer pp = stack.mallocPointer(1);

        final MDBVal rwKey = mallocStack(stack);
        final MDBVal rwVal = mallocStack(stack);

        E(mdb_txn_begin(env, NULL, 0, pp));
        final long tx = pp.get(0);

        E(mdb_cursor_open(tx, db, pp));
        final long c = pp.get(0);

        final int flags = sequential ? MDB_APPEND : 0;
        final int rndByteMax = RND_MB.length - valSize;
        int rndByteOffset = 0;
        for (final int key : keys) {
          stack.push();
          if (intKey) {
            rwKey.mv_data(stack.malloc(4).putInt(0, key));
          } else {
            rwKey.mv_data(stack.ASCII(padKey(key), false));
          }
          if (valRandom) {
            final ByteBuffer rnd = stack.malloc(valSize).put(RND_MB,
                                                             rndByteOffset,
                                                             valSize);
            rnd.flip();
            rwVal.mv_data(rnd);
            rndByteOffset += valSize;
            if (rndByteOffset >= rndByteMax) {
              rndByteOffset = 0;
            }
          } else {
            rwVal.mv_data(stack.malloc(valSize).putInt(0, key));
          }

          E(mdb_cursor_put(c, rwKey, rwVal, flags));
          stack.pop();
        }

        mdb_cursor_close(c);
        mdb_txn_commit(tx);
      }
    }

  }

  public static class Reader extends CommonLmdbLwjgl {

    long c;
    long txn;

    @Override
    public void setup(File tempDir, int numEntries) throws IOException {
      super.setup(tempDir, numEntries, false);
      super.write();

      try (MemoryStack stack = stackPush()) {
        final PointerBuffer pp = stack.mallocPointer(1);

        E(mdb_txn_begin(env, NULL, MDB_RDONLY, pp));
        txn = pp.get(0);

        E(mdb_cursor_open(txn, db, pp));
        c = pp.get(0);
      }
    }

    @Override
    public void teardown() throws IOException {
      mdb_cursor_close(c);
      mdb_txn_abort(txn);
      super.teardown();
    }
  }

  public static class Writer extends CommonLmdbLwjgl {

    /**
     * Whether <code>MDB_NOSYNC</code> is used.
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
