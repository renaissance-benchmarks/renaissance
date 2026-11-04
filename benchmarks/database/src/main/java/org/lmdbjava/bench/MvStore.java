package org.lmdbjava.bench;

import java.io.File;
import java.nio.ByteOrder;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;

import org.agrona.MutableDirectBuffer;
import org.agrona.concurrent.UnsafeBuffer;
import org.h2.mvstore.MVMap;
import org.h2.mvstore.MVStore;

public class MvStore extends DatabaseManager<MvStore.Writer, MvStore.Reader> {

  private MVStore store;
  private MVMap<byte[], byte[]> map;

  public static MvStore setup(File scratchDir, int threads, Boolean runInMemory) {
    MvStore instance = new MvStore(scratchDir, threads, runInMemory);
    instance.initializeSharedDatabase();
    return instance;
  }

  private MvStore(File scratchDir, int threads, Boolean runInMemory) {
    super(scratchDir, threads, runInMemory);
  }

  @Override
  protected void initializeSharedDatabase() {
    if (runInMemory) {
      System.out.println("[" + getDatabaseInfo() + "] Running IN MEMORY");
      this.store = new MVStore.Builder()
              .fileName((String) null)
              .autoCommitDisabled()
              .open();
      this.dbFile = null;
    } else {
      this.dbFile = new File(scratchDir, "MvStore.db");
      if (dbFile.exists()) {
        dbFile.delete();
      }
      System.out.println("[" + getDatabaseInfo() + "] Running ON DISK: " + dbFile.getAbsolutePath());
      this.store = new MVStore.Builder()
              .fileName(dbFile.getAbsolutePath())
              .autoCommitDisabled()
              .open();
    }
    this.map = store.openMap("ba2ba_v2");
  }

  @Override
  protected void closeDatabase() {
    if (store != null) {
      store.close();
    }
    // Delete the database file to prevent size accumulation
    if (dbFile != null && dbFile.exists()) {
      boolean deleted = dbFile.delete();
      if (!deleted) {
        System.err.println("[" + getDatabaseInfo() + "] Warning: Could not delete database file");
      }
    }
  }

  @Override
  protected String getDatabaseInfo() {
    return "MvStore";
  }

  @Override
  public Writer createWriter() {
    return new Writer(threads, createThreadPool(), map, store);
  }

  @Override
  public Reader createReader() {
    return new Reader(threads, createThreadPool(), map);
  }

  // ==================== Writer ====================
  public static class Writer extends DatabaseManager.Worker {
    private final MVMap<byte[], byte[]> map;
    private final MVStore store;

    Writer(int threads, ExecutorService threadPool, MVMap<byte[], byte[]> map, MVStore store) {
      super(threads,threadPool);
      this.map = map;
      this.store = store;
    }

    /**
     * Write key-value pairs with overwrites using MutableDirectBuffer
     * @param keys array per thread: keys[threadIndex][keyIndex]
     * @param values array per thread per key: values[threadIndex][keyIndex][valueSequenceIndex]
     *               value -1 means delete
     */
    public void write(int[][] keys, int[][][] values) throws InterruptedException {
      final CompletionService<Void> executor = new ExecutorCompletionService<>(threadPool);

      for (int t = 0; t < threads; t++) {
        final int threadIndex = t;

        executor.submit(() -> {
          final byte[] keyBytes = new byte[Integer.BYTES];
          final byte[] valueBytes = new byte[Integer.BYTES];
          final MutableDirectBuffer keyBuffer = new UnsafeBuffer(keyBytes);
          final MutableDirectBuffer valueBuffer = new UnsafeBuffer(valueBytes);

          int[] threadKeys = keys[threadIndex];
          int[][] threadValues = values[threadIndex];

          for (int k = 0; k < threadKeys.length; k++) {
            int key = threadKeys[k];
            int[] valueSequence = threadValues[k];

            keyBuffer.putInt(0, key, ByteOrder.LITTLE_ENDIAN);

            for (int value : valueSequence) {
              if (value == -1) {
                // MVStore requires copy for key
                map.remove(Arrays.copyOf(keyBytes, Integer.BYTES));
              } else {
                valueBuffer.putInt(0, value, ByteOrder.LITTLE_ENDIAN);
                // MVStore requires copies
                map.put(Arrays.copyOf(keyBytes, Integer.BYTES),
                        Arrays.copyOf(valueBytes, Integer.BYTES));
              }
            }
          }
          return null;
        });
      }

      for (int i = 0; i < threads; i++) {
        executor.take();
      }
      // Commit after all threads finish
      store.commit();
    }
  }

  // ==================== Reader ====================
  public static class Reader extends DatabaseManager.Worker {
    private final MVMap<byte[], byte[]> map;

    Reader(int threads, ExecutorService threadPool, MVMap<byte[], byte[]> map) {
      super(threads, threadPool);
      this.map = map;
    }

    /**
     * Read values for given keys using MutableDirectBuffer
     * @param keys array per thread: keys[threadIndex][keyIndex]
     * @return map of key -> value (only existing keys)
     */
    public Map<Integer, Integer> read(int[][] keys) throws InterruptedException, ExecutionException {
      final CompletionService<Map<Integer, Integer>> executor = new ExecutorCompletionService<>(threadPool);

      for (int t = 0; t < threads; t++) {
        final int threadIndex = t;

        executor.submit(() -> {
          final byte[] keyBytes = new byte[Integer.BYTES];
          final MutableDirectBuffer keyBuffer = new UnsafeBuffer(keyBytes);
          final MutableDirectBuffer valueBuffer = new UnsafeBuffer(new byte[Integer.BYTES]);

          int[] threadKeys = keys[threadIndex];
          Map<Integer, Integer> localResult = new HashMap<>();

          for (int key : threadKeys) {
            keyBuffer.putInt(0, key, ByteOrder.LITTLE_ENDIAN);

            byte[] valueBytes = map.get(keyBytes);
            if (valueBytes != null) {
              valueBuffer.wrap(valueBytes);
              int value = valueBuffer.getInt(0, ByteOrder.LITTLE_ENDIAN);
              localResult.put(key, value);
            }
          }
          return localResult;
        });
      }

      final Map<Integer, Integer> result = new HashMap<>();
      for (int i = 0; i < threads; i++) {
        Map<Integer, Integer> threadResult = executor.take().get();
        result.putAll(threadResult);
      }

      return result;
    }
  }
}