package org.renaissance;

/** Base class for plugins that gather other metrics.
 *  <p>
 *  Subclasses must have a zero arguments constructor.
 */
public abstract class Plugin {
  /** Called once after the plugin is created.
   */
  public abstract void onCreation();

  /** Called before a benchmark starts executing.
   */
  public void onStart(Policy policy) {
  }

  public abstract void beforeIteration(Policy policy);

  public abstract void afterIteration(Policy policy, long duration);

  /** Called after the benchmark is done executing.
   */
  public void onTermination(Policy policy) {
  }

  /** Called once after all benchmarks are done executing.
   */
  public void onExit() {
  }
}
