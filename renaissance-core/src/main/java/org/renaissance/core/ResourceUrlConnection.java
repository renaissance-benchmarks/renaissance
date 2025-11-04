package org.renaissance.core;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.net.URLConnection;
import java.net.URLStreamHandler;
import java.net.URLStreamHandlerFactory;

/**
 * Minimalistic {@link URLConnection} to enable loading classes from resource
 * JAR files. Multiple URL connections may be open simultaneously, but it does
 * not pay off to cache the content. The JAR files will be stored uncompressed
 * and the I/O to the main bundle will be cached by the operating system.
 */
class ResourceUrlConnection extends URLConnection {
  static final String PROTOCOL = "resource";

  static final URLStreamHandlerFactory FACTORY = protocol -> {
    if (!PROTOCOL.equals(protocol)) {
      return null;
    }

    return new URLStreamHandler() {
      @Override
      protected URLConnection openConnection(URL url) throws IOException {
        return new ResourceUrlConnection(url);
      }
    };
  };

  //

  /** A value of -1 indicates unknown length. */
  private int contentLength = -1;

  ResourceUrlConnection(URL url) {
    super(url);
  }

  @Override
  public void connect() throws IOException {
    if (connected) {
      return;
    }

    // Determine content length but do not load it yet.
    try (InputStream resourceStream = getCoreResourceAsStream(url.getPath())) {
      if (resourceStream == null) {
        throw new FileNotFoundException(url.getPath());
      }

      contentLength = resourceStream.available();
      connected = true;
    }
  }


  @Override
  public InputStream getInputStream() throws IOException {
    if (!connected) {
      connect();
    }

    assert connected;
    return getCoreResourceAsStream(url.getPath());
  }

  private static InputStream getCoreResourceAsStream(String file) {
    // Use the class loader used to load the core classes.
    return ModuleLoader.class.getResourceAsStream(file);
  }

  @Override
  public String getContentType() {
    // This is called rarely, so we don't need to keep it in the instance.
    final String pathLowercase = url.getPath().toLowerCase();
    if (pathLowercase.endsWith(".jar")) {
      return "application/java-archive";
    } else if (pathLowercase.endsWith(".class")) {
      return "application/java-bytecode";
    } else {
      return "application/octet-stream";
    }
  }

  @Override
  public long getContentLengthLong() {
    // Also used internally by getContentLength(). We use an integer
    // for content length anyway, so it is enough to override this.
    return contentLength;
  }

}
