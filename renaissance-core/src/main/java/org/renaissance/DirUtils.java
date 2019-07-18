package org.renaissance;

import java.io.IOException;
import java.nio.file.*;
import java.nio.file.attribute.BasicFileAttributes;

final class DirUtils {

  public static void deleteTempDir(Path dirPath) {
    try {
      deleteRecursively(dirPath);
    } catch (Throwable t) {
      System.err.println("Error removing temp directory! " + t.getMessage());
    }
  }


  private static void deleteRecursively(final Path dirPath) throws IOException {
    Files.walkFileTree(dirPath, new SimpleFileVisitor<Path>() {
      @Override
      public FileVisitResult visitFile(Path file, BasicFileAttributes attrs)
      throws IOException {
        return delete(file);
      }


      @Override
      public FileVisitResult postVisitDirectory(Path dir, IOException exc) throws IOException {
        return delete(dir);
      }


      private FileVisitResult delete(Path path) throws IOException {
        Files.delete(path);
        return FileVisitResult.CONTINUE;
      }
    });
  }


  public static Path generateTempDir(String name) {
    try {
      return Files.createTempDirectory(Paths.get("."), name);

    } catch (IOException e) {
      System.err.println("Error creating temp directory! " + e.getMessage());
    }

    return null;
  }

}
