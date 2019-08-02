package org.renaissance.core;

public final class ModuleLoadingException extends Exception {
  private static final long serialVersionUID = 1L;

  public ModuleLoadingException(String message) {
    super(message);
  }

  public ModuleLoadingException(String message, Throwable cause) {
    super(message, cause);
  }
}