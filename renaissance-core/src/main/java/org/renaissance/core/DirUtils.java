package org.renaissance.core;

import java.io.IOException;
import java.nio.file.DirectoryNotEmptyException;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.nio.file.Files.createTempDirectory;

public final class DirUtils {

  private static final Logger logger = Logging.getPackageLogger(DirUtils.class);

  public static boolean cleanRecursively(final Path rootDir) throws IOException {
    return deleteRecursively(rootDir, false);
  }

  public static boolean deleteRecursively(final Path rootDir) throws IOException {
    return deleteRecursively(rootDir, true);
  }

  private static boolean deleteRecursively(
    final Path path, boolean deletePath
  ) throws IOException {
    if (Files.notExists(path, LinkOption.NOFOLLOW_LINKS)) {
      return true;
    }

    boolean result = true;
    if (Files.isDirectory(path, LinkOption.NOFOLLOW_LINKS)) {
      // Delete directory contents so that we can delete it.
      for (Path entry : listDirectory(path)) {
        // Always delete and only then aggregate the result.
        result &= deleteRecursively(entry, true);
      }

      // FALL THROUGH: the directory should be empty at this point.
    }

    if (deletePath) {
      try {
        Files.deleteIfExists(path);

      } catch (DirectoryNotEmptyException ex) {
        logger.fine(String.format("could not delete non-empty directory: %s", path));

        // Log the leftovers if desired.
        if (logger.isLoggable(Level.FINER)) {
          listDirectory(path).forEach(entry -> {
            final String kind = Files.isDirectory(entry) ? "directory" : "file";
            logger.finer(String.format("leftover %s: %s", kind, entry));
          });
        }

        return false;

      } catch (IOException ex) {
        final String kind = Files.isDirectory(path) ? "directory" : "file";
        logger.finer(String.format("failed to delete %s: %s", kind, path));
        return false;
      }
    }

    return result;
  }

  private static final Comparator<Path> directoriesFirstComparator = (l, r) -> {
    final boolean leftIsDir = Files.isDirectory(l, LinkOption.NOFOLLOW_LINKS);
    final boolean rightIsDir = Files.isDirectory(r, LinkOption.NOFOLLOW_LINKS);

    if (leftIsDir && !rightIsDir) {
      return -1;
    } else if (!leftIsDir && rightIsDir) {
      return 1;
    } else {
      return l.compareTo(r);
    }
  };

  /** Lists files and directories in a directory. */
  static List<Path> listDirectory(final Path dir) throws IOException {
    try (
      final Stream<Path> paths = Files.list(dir).sorted(directoriesFirstComparator)
    ) {
      // Take a snapshot of the directory contents so that we don't
      // walk over files that may appear on NFS when deleting open file.
      return paths.collect(Collectors.toList());
    }
  }

  /** Lists (only) files in a directory hierarchy. */
  static List<Path> listRecursively(final Path path) throws IOException {
    if (Files.isDirectory(path, LinkOption.NOFOLLOW_LINKS)) {
      List<Path> result = new ArrayList<>();
      for (Path entry : listDirectory(path)) {
        result.addAll(listRecursively(entry));
      }

      return result;
    } else {
      return Collections.singletonList(path);
    }
  }

  public static Path createScratchDirectory(Path base, String prefix, boolean keepOnExit)
  throws IOException {
    String ts = DateTimeFormatter.ofPattern("HHmmss").format(LocalDateTime.now());
    String tsPrefix = String.format("%s%s-", prefix, ts);

    Path scratchDir = createTempDirectory(base, tsPrefix).normalize();
    if (!keepOnExit) {
      Cleaner.deleteOnExit(scratchDir);
    }

    return scratchDir;
  }

}
