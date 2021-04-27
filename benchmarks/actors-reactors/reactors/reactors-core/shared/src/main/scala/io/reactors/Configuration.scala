package io.reactors






trait Configuration {
  def int(path: String): Int
  def string(path: String): String
  def double(path: String): Double
  def list(path: String): Seq[Configuration]
  def children(path: String): Seq[Configuration]
  def withFallback(other: Configuration): Configuration
}


object Configuration {
  private[reactors] trait Factory {
    def parse(content: String): Configuration
    def empty: Configuration
  }

  private[reactors] val configurationFactory = Platform.configurationFactory

  def parse(content: String): Configuration = configurationFactory.parse(content)

  def empty: Configuration = configurationFactory.empty
}
