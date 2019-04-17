/* scala-stm - (c) 2009-2012, Stanford University, PPL */

package scala.concurrent.stm;

public class TestException extends RuntimeException {
    public TestException() {
        super("Expected failure");
    }
}
