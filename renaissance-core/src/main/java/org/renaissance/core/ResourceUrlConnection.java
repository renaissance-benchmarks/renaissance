package org.renaissance.core;

import java.io.ByteArrayInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.lang.ref.WeakReference;
import java.net.URL;
import java.net.URLConnection;
import java.net.URLStreamHandler;
import java.net.URLStreamHandlerFactory;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

/**
 * An implementation of a {@link URLConnection} for resources. Serves primarily
 * to allow loading classes from resource JAR files. Because a single resource
 * may be accessed simultaneously from multiple connections, this class caches
 * the resource contents so that it can be shared between active connections.
 * The cached content is released after all connections using it are closed.
 */
class ResourceUrlConnection extends URLConnection {
  static final String PROTOCOL = "resource";

  static final URLStreamHandlerFactory FACTORY = protocol -> {
    if (!PROTOCOL.equals(protocol)) {
      return null;
    }

    return new URLStreamHandler() {
      /** Cache shared by connections created by this handler. */
      final ConcurrentMap<String, WeakReference<byte[]>> sharedCache = new ConcurrentHashMap<>();

      @Override
      protected URLConnection openConnection(URL url) throws IOException {
        return new ResourceUrlConnection(url, sharedCache);
      }
    };
  };

  //

  /**
   * Content cache. The keys are @{link URL} paths (without anchor fragments),
   * use strong references, and are never removed, even if the corresponding
   * weak reference is cleared. An entry without content means that the
   * resource actually exists and just needs to be loaded.
   */
  private final ConcurrentMap<String, WeakReference<byte[]>> weakContentByPath;

  /** A value of -1 indicates unknown length. */
  private int contentLength = -1;

  ResourceUrlConnection(
    URL url, ConcurrentMap<String, WeakReference<byte[]>> sharedCache
  ) {
    super(url);
    weakContentByPath = sharedCache;
  }

  @Override
  public void connect() throws IOException {
    if (connected) {
      return;
    }

    final String urlPath = url.getPath();

    // If the resource is still cached, fill the content length.
    final WeakReference<byte[]> weakContent = weakContentByPath.get(urlPath);
    if (weakContent != null) {
      byte[] content = weakContent.get();
      if (content != null) {
        contentLength = content.length;
        connected = true;
        return;
      }

      // FALL THROUGH: The resource is not in the cache anymore.
    }

    //
    // The resource is not in cache, determine its length but do not load it
    // yet. We put a dummy entry in the cache so that we do not have to worry
    // about it in the getInputStream() method.
    //
    try (InputStream resourceStream = getCoreResourceAsStream(urlPath)) {
      if (resourceStream == null) {
        throw new FileNotFoundException(urlPath);
      }

      // Insert an entry marking that we have seen the resource.
      weakContentByPath.putIfAbsent(urlPath, new WeakReference<>(null));
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
    final String urlPath = url.getPath();

    // Connected implies that the cache has an entry, meaning
    // the resource exists, but not that it is actually cached.
    final byte[] cachedContent = weakContentByPath.get(urlPath).get();
    if (cachedContent != null) {
      return new ByteArrayInputStream(cachedContent);
    }

    // The content is not in the cache, load it.
    try (InputStream resourceStream = getCoreResourceAsStream(urlPath)) {
      assert resourceStream != null : "the resource stream is expected to exist";

      final byte[] content = resourceStream.readAllBytes();
      weakContentByPath.put(urlPath, new WeakReference<>(content));
      return new ByteArrayInputStream(content);
    }
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
