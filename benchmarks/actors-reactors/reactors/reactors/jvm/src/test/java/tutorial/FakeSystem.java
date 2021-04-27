package tutorial;



import java.util.concurrent.*;



public class FakeSystem {
  public class Out {
    public LinkedTransferQueue<Object> queue = new LinkedTransferQueue<>();
    public void println(Object x) {
      queue.add(x);
    }
  }
  public Out out = new Out();
}
