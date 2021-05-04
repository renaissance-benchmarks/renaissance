package org.renaissance.core;

import java.io.IOException;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.logging.Logger;

import static java.nio.file.Files.createTempDirectory;

public final class DirUtils {

  private static final Logger logger = Logging.getPackageLogger(DirUtils.class);

  public static void cleanRecursively(final Path rootDir) throws IOException {
    deleteRecursively(rootDir, false);
  }

  public static void deleteRecursively(final Path rootDir) throws IOException {
    deleteRecursively(rootDir, true);
  }

  private static void deleteRecursively(final Path rootDir, boolean deleteRoot) throws IOException {
    Files.walkFileTree(rootDir, new SimpleFileVisitor<Path>() {
      @Override
      public FileVisitResult visitFile(Path file, BasicFileAttributes attrs)
      throws IOException {
        Files.delete(file);
        return FileVisitResult.CONTINUE;
      }


      @Override
      public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
        if (deleteRoot || !rootDir.equals(dir)) {
          Files.delete(dir);
        }

        return FileVisitResult.CONTINUE;
      }
    });
  }


  public static Path createScratchDirectory(Path base, String prefix, boolean keepOnExit) throws IOException {
    String ts = DateTimeFormatter.ofPattern("HHmmss").format(LocalDateTime.now());
    String tsPrefix = String.format("%s%s-", prefix, ts);

    Path scratchDir = createTempDirectory(base, tsPrefix).normalize();
    if (!keepOnExit) {
      Runtime.getRuntime().addShutdownHook(new Thread (() -> {
        logger.fine(() -> "Deleting scratch directory: " + printable(scratchDir));
        try {
          deleteRecursively(scratchDir);
        } catch (IOException e) {
          // Just a notification. This should be rare and is not critical.
          logger.warning(String.format(
            "Error deleting scratch directory %s: %s", printable(scratchDir), e.getMessage()
          ));
        }
      }));
    }

    return scratchDir;
  }

  private static Path printable(Path path) {
    return path.toAbsolutePath().normalize();
  }

}
