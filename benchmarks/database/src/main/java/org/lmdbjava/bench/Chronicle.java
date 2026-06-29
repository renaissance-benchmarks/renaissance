package org.lmdbjava.bench;

import java.io.File;
import java.io.IOException;
import java.nio.ByteOrder;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.CompletionService;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorCompletionService;
import java.util.concurrent.ExecutorService;

import net.openhft.chronicle.map.ChronicleMap;
import org.agrona.MutableDirectBuffer;
import org.agrona.concurrent.UnsafeBuffer;

public class Chronicle extends DatabaseManager<Chronicle.Writer, Chronicle.Reader> {

  private ChronicleMap<byte[], byte[]> map;
  private final int valueSize;
  private final int entryCount;

  public static Chronicle setup(File scratchDir, int threads, int valueSize, int entryCount, Boolean runInMemory) {
    Chronicle instance = new Chronicle(scratchDir, threads, valueSize, entryCount, runInMemory);
    instance.initializeSharedDatabase();
    return instance;
  }

  private Chronicle(File scratchDir, int threads, int valueSize, int entryCount, Boolean runInMemory) {
    super(scratchDir, threads, runInMemory);
    this.valueSize = valueSize;
    this.entryCount = entryCount;
  }

  @Override
  protected void initializeSharedDatabase() {
    if (runInMemory) {
      System.out.println("[" + getDatabaseInfo() + "] Running IN MEMORY");
      this.map = ChronicleMap.of(byte[].class, byte[].class)
              .constantKeySizeBySample(new byte[Integer.BYTES])
              .constantValueSizeBySample(new byte[valueSize])
              .entries(entryCount)
              .create();
      this.dbFile = null;
    } else {
      this.dbFile = new File(scratchDir, "Chronicle.map");
      if (dbFile.exists()) {
        dbFile.delete();
      }
      System.out.println("[" + getDatabaseInfo() + "] Running ON DISK: " + dbFile.getAbsolutePath());
      try {
        this.map = ChronicleMap.of(byte[].class, byte[].class)
                .constantKeySizeBySample(new byte[Integer.BYTES])
                .constantValueSizeBySample(new byte[valueSize])
                .entries(entryCount)
                .createPersistedTo(dbFile);
      } catch (IOException ex) {
        throw new IllegalStateException("Unable to create Chronicle map", ex);
      }
    }
  }

  @Override
  protected void closeDatabase() {
    if (map != null) {
      map.close();
    }
  }

  @Override
  protected String getDatabaseInfo() {
    return "Chronicle";
  }

  @Override
  public Writer createWriter() {
    return new Writer(threads, createThreadPool(), map);
  }

  @Override
  public Reader createReader() {
    return new Reader(threads, createThreadPool(),  map);
  }

  // ==================== Writer ====================
  public static class Writer extends DatabaseManager.Worker {
    private final ChronicleMap<byte[], byte[]> map;

    Writer(int threads, ExecutorService threadPool, ChronicleMap<byte[], byte[]> map) {
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
                map.remove(keyBytes.clone());
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
    private final ChronicleMap<byte[], byte[]> map;

    Reader(int threads,ExecutorService threadPool, ChronicleMap<byte[], byte[]> map) {
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