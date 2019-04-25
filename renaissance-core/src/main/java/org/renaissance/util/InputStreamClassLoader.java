package org.renaissance.util;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.logging.Logger;

public class InputStreamClassLoader extends URLClassLoader {

  private static final URL[] URL_ARRAY_TYPE = new URL[0];

  public InputStreamClassLoader(ClassLoader parent, InputStream ... inputJars) throws IOException {
    super(extractFromInputStream(inputJars), parent);
  }
  
  private static URL[] extractFromInputStream(InputStream[] inputJars) throws IOException {
    Logger logger = Logging.getMethodLogger(InputStreamClassLoader.class, "extractFromInputStream");

    Path baseDir = Paths.get(".");
    Path baseUnpackDir = Files.createTempDirectory(baseDir, "jars-");
    baseUnpackDir.toFile().deleteOnExit();
    List<URL> resultUrls = new ArrayList<>(inputJars.length);
    
    for (InputStream inputJar : inputJars) {
      Path unpackedTargetPath = Files.createTempFile(baseUnpackDir, "cp-", ".jar");
      File unpackedTarget = unpackedTargetPath.toFile();
      unpackedTarget.deleteOnExit();
      OutputStream unpackedOutStream = new FileOutputStream(unpackedTarget);

      logger.fine(String.format("Extracting %s into %s", inputJar, unpackedTargetPath));
      
      byte[] buffer = new byte[8 * 1024];
      int bytesRead;
      while ((bytesRead = inputJar.read(buffer)) != -1) {
        unpackedOutStream.write(buffer, 0, bytesRead);
      }
      
      unpackedOutStream.close();
      
      resultUrls.add(unpackedTargetPath.toUri().toURL());
    }

    return resultUrls.toArray(URL_ARRAY_TYPE);
  }
}
