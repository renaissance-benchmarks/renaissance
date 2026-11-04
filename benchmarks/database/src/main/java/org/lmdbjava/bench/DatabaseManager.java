package org.lmdbjava.bench;

import java.io.File;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

/**
 * Abstract base for database managers that handle shared DB lifecycle
 * @param <W> Writer type
 * @param <R> Reader type
 */
public abstract class DatabaseManager<W extends DatabaseManager.Worker,
        R extends DatabaseManager.Worker>
        extends Common {

    protected File dbFile;

    protected DatabaseManager(File scratchDir, int threads, Boolean runInMemory) {
        super(scratchDir, threads, runInMemory);
    }

    /**
     * Initialize the shared database - called once by the manager
     */
    protected abstract void initializeSharedDatabase();

    /**
     * Close the shared database
     */
    protected abstract void closeDatabase();

    /**
     * Get database info for logging
     */
    protected abstract String getDatabaseInfo();

    /**
     * Create a writer that uses the shared database
     */
    public abstract W createWriter();

    /**
     * Create a reader that uses the shared database
     */
    public abstract R createReader();

    /**
     * Close the database and report size if requested
     */
    public void close(boolean reportSpace) {
        if (reportSpace && !runInMemory) {
            reportDatabaseSize(dbFile, getDatabaseInfo(), "before close");
        }
        closeDatabase();
    }

    public void close() {
        close(false);
    }

    public File getDbFile() {
        return dbFile;
    }

    /**
     * Base class for workers (Reader/Writer) that operate on shared database
     */
    public abstract static class Worker {
        protected final int threads;
        protected final ExecutorService threadPool;

        protected Worker(int threads, ExecutorService threadPool) {
            this.threads = threads;
            this.threadPool = threadPool;
        }

        public void shutdown() {
            Common.shutdown(threadPool);
        }
    }
}