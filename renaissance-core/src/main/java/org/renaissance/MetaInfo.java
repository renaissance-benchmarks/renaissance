package org.renaissance;

import java.io.IOException;
import java.io.InputStream;
import java.net.URL;
import java.util.Enumeration;
import java.util.jar.Manifest;
import java.util.jar.Attributes;

public class MetaInfo {
  private static final String UNKNOWN_VERSION = "?.?.?";
  private static final String VERSION_ATTRIBUTE = "Renaissance-Version";

  public static String getRenaissanceVersion() {
    // It should be enough to call the following to access the main manifest:
    // new Manifest(MetaInfo.class.getResourceAsStream("/META-INF/MANIFEST.MF"))
    // but because of https://bugs.openjdk.java.net/browse/JDK-8201636
    // we need to iterate over all manifests to find the right one

    Enumeration<URL> manifestUrls;
    try {
      manifestUrls = MetaInfo.class.getClassLoader().getResources("META-INF/MANIFEST.MF");
    } catch (IOException e) {
      return UNKNOWN_VERSION;
    }

    while (manifestUrls.hasMoreElements()) {
      URL url = manifestUrls.nextElement();
      try {
        Manifest manifest = loadManifestFromURL(url);
        Attributes mainAttributes = manifest.getMainAttributes();
        String version = mainAttributes.getValue(VERSION_ATTRIBUTE);
        if (version != null) {
          return version;
        }
      } catch (IOException e) {
        // Ignore exceptions here
      }
    }
    return UNKNOWN_VERSION;
  }

  private static Manifest loadManifestFromURL(URL url) throws IOException {
      InputStream manifestStream = null;
      try {
        manifestStream = url.openStream();
        return new Manifest(manifestStream);
      } catch (IOException e) {
        throw e;
      } finally {
        manifestStream.close();
      }
  }
}
