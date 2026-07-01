package org.lmdbjava.bench;

import java.io.File;
import java.nio.ByteOrder;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;

import org.agrona.MutableDirectBuffer;
import org.agrona.concurrent.UnsafeBuffer;
import org.mapdb.BTreeMap;
import org.mapdb.DB;
import org.mapdb.DBMaker;
import static org.mapdb.DBMaker.fileDB;
import static org.mapdb.Serializer.BYTE_ARRAY;

public class MapDb extends DatabaseManager<MapDb.Writer, MapDb.Reader> {

  private DB db;
  private BTreeMap<byte[], byte[]> map;

  public static MapDb setup(File scratchDir, int threads, Boolean runInMemory) {
    MapDb instance = new MapDb(scratchDir, threads, runInMemory);
    instance.initializeSharedDatabase();
    return instance;
  }

  private MapDb(File scratchDir, int threads, Boolean runInMemory) {
    super(scratchDir, threads, runInMemory);
  }

  @Override
  protected void initializeSharedDatabase() {
    if (this.runInMemory) {
      System.out.println("[" + getDatabaseInfo() + "] Running IN MEMORY");
      this.db = DBMaker.memoryDB().make();
    } else {
      this.dbFile = new File(scratchDir, "MapDb.db");
      System.out.println("[" + getDatabaseInfo() + "] Running ON DISK: " + dbFile.getAbsolutePath());
      this.db = fileDB(dbFile)
              .fileMmapEnable()
              .make();
    }

    this.map = db.treeMap("ba2ba_v2")
            .keySerializer(BYTE_ARRAY)
            .valueSerializer(BYTE_ARRAY)
            .createOrOpen();
  }

  @Override
  protected void closeDatabase() {
    if (db != null) {
      map.close();
      db.close();
    }
    if (dbFile != null && dbFile.exists()) {
      boolean deleted = dbFile.delete();
      if (!deleted) {
        System.err.println("[" + getDatabaseInfo() + "] Warning: Could not delete database file");
      }
    }
  }

  @Override
  protected String getDatabaseInfo() {
    return "MapDb";
  }

  @Override
  public Writer createWriter() {
    return new Writer(threads, createThreadPool(), map);
  }

  @Override
  public Reader createReader() {
    return new Reader(threads, createThreadPool(), map);
  }

  // ==================== Writer ====================
  public static class Writer extends DatabaseManager.Worker {
    private final BTreeMap<byte[], byte[]> map;

    Writer(int threads, ExecutorService threadPool, BTreeMap<byte[], byte[]> map) {
      super(threads, threadPool);
      this.map = map;
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
          // Each thread has its own buffers
          final byte[] keyBytes = new byte[Integer.BYTES];
          final byte[] valueBytes = new byte[Integer.BYTES];
          final MutableDirectBuffer keyBuffer = new UnsafeBuffer(keyBytes);
          final MutableDirectBuffer valueBuffer = new UnsafeBuffer(valueBytes);

          int[] threadKeys = keys[threadIndex];
          int[][] threadValues = values[threadIndex];

          for (int k = 0; k < threadKeys.length; k++) {
            int key = threadKeys[k];
            int[] valueSequence = threadValues[k];

            // Convert key to bytes
            keyBuffer.putInt(0, key, ByteOrder.LITTLE_ENDIAN);

            for (int value : valueSequence) {
              if (value == -1) {
                map.remove(keyBytes.clone());  // clone because MapDB may store reference
              } else {
                valueBuffer.putInt(0, value, ByteOrder.LITTLE_ENDIAN);
                map.put(keyBytes.clone(), valueBytes.clone());
              }
            }
          }
          return null;
        });
      }

      for (int i = 0; i < threads; i++) {
        executor.take();
      }
    }
  }

  // ==================== Reader ====================
  public static class Reader extends DatabaseManager.Worker {
    private final BTreeMap<byte[], byte[]> map;

    Reader(int threads, ExecutorService threadPool, BTreeMap<byte[], byte[]> map) {
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

      // Merge all results after threads finish
      final Map<Integer, Integer> result = new HashMap<>();
      for (int i = 0; i < threads; i++) {
        Map<Integer, Integer> threadResult = executor.take().get();
        result.putAll(threadResult);
      }

      return result;
    }
  }
}