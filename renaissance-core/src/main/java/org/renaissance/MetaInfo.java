package org.renaissance;

import java.io.IOException;
import java.io.InputStream;
import java.util.jar.Manifest;
import java.util.jar.Attributes;

public class MetaInfo {
  private static final String UNKNOWN_VERSION = "?.?.?";

  public static String getRenaissanceVersion() {
    InputStream manifestStream = MetaInfo.class.getResourceAsStream("/META-INF/MANIFEST.MF");
    if (manifestStream == null) {
      return UNKNOWN_VERSION;
    }

    try {
      Manifest manifest = new Manifest(manifestStream);
      Attributes mainAttributes = manifest.getMainAttributes();
      String version = mainAttributes.getValue("Renaissance-Version");
      manifestStream.close();

      if (version == null) {
        return UNKNOWN_VERSION;
      }
      return version;
    } catch (IOException e) {
      return UNKNOWN_VERSION;
    }
  }
}
