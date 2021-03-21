package tutorial;



/*!begin-include!*/
/*!begin-code!*/
import io.reactors.japi.*;
/*!end-code!*/
/*!end-include(reactors-java-event-streams-import.html)!*/
import java.util.ArrayList;
import java.util.Arrays;
import org.junit.Assert;
import org.junit.Test;



public class event_streams {
  private Events<String> createEventStream() {
    return Events.never();
  }

  static FakeSystem System = new FakeSystem();

  @Test
  public void eventsOnEvent() {
    /*!begin-include!*/
    /*!begin-code!*/
    Events<String> myEvents = createEventStream();
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-create.html)!*/

    /*!begin-include!*/
    /*!begin-code!*/
    myEvents.onEvent(x -> System.out.println(x));
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-on-event.html)!*/
  }

  /*!begin-include!*/
  /*!begin-code!*/
  public <T> void trace(Events<T> events) {
    events.onEvent(x -> System.out.println(x));
  }
  /*!end-code!*/
  /*!end-include(reactors-java-event-streams-trace.html)!*/

  @Test
  public void emitterReact() {
    /*!begin-include!*/
    /*!begin-code!*/
    Events.Emitter<Integer> emitter = Events.emitter();
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-emitter.html)!*/

    /*!begin-include!*/
    /*!begin-code!*/
    final int[] luckyNumber = new int[] { 0 };
    emitter.onEvent(x -> luckyNumber[0] = x);
    emitter.react(7);
    Assert.assertEquals(7, luckyNumber[0]);
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-lucky-number.html)!*/
  }

  @Test
  public void emitterLifecycle() {
    /*!begin-include!*/
    /*!begin-code!*/
    ArrayList<Integer> seen = new ArrayList<Integer>();
    ArrayList<String> errors = new ArrayList<String>();
    int[] done = new int[] { 0 };
    Events.Emitter<Integer> e = Events.emitter();
    e.onReaction(Observer.create(
      x -> seen.add(x),
      t -> errors.add(t.getMessage()),
      () -> done[0]++));
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-observer.html)!*/

    /*!begin-include!*/
    /*!begin-code!*/
    e.react(1);
    Assert.assertEquals(seen, new ArrayList<Integer>(Arrays.asList(1)));
    e.react(2);
    Assert.assertEquals(seen, new ArrayList<Integer>(Arrays.asList(1, 2)));
    Assert.assertEquals(done[0], 0);
    e.except(new Exception("^_^"));
    Assert.assertEquals(errors, new ArrayList<String>(Arrays.asList("^_^")));
    e.react(3);
    Assert.assertEquals(seen, new ArrayList<Integer>(Arrays.asList(1, 2, 3)));
    Assert.assertEquals(done[0], 0);
    e.unreact();
    Assert.assertEquals(done[0], 1);
    e.react(4);
    e.except(new Exception("o_O"));
    Assert.assertEquals(seen, new ArrayList<Integer>(Arrays.asList(1, 2, 3)));
    Assert.assertEquals(errors, new ArrayList<String>(Arrays.asList("^_^")));
    Assert.assertEquals(done[0], 1);
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-observer-test.html)!*/
  }

  @Test
  public void onX() {
    /*!begin-include!*/
    /*!begin-code!*/
    Events.Emitter<String> e = Events.emitter();
    e.onEventOrDone(
      x -> System.out.println(x),
      () -> System.out.println("she's done, mate!"));
    e.onDone(() -> System.out.println("done!"));
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-on-x.html)!*/

    e.react("ok");
    e.unreact();

    try {
      Assert.assertEquals("ok", System.out.queue.take());
      Assert.assertEquals("she's done, mate!", System.out.queue.take());
      Assert.assertEquals("done!", System.out.queue.take());
    } catch (Exception t) {
      throw new RuntimeException(t);
    }
  }

  @Test
  public void onEventSquareSum() {
    /*!begin-include!*/
    /*!begin-code!*/
    int[] squareSum = new int[] { 0 };
    Events.Emitter<Integer> e = Events.emitter();
    e.onEvent(x -> squareSum[0] += x * x);
    for (int i = 0; i < 5; i++) e.react(i);
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-sum-var.html)!*/

    Assert.assertEquals(30, squareSum[0]);

    /*!begin-include!*/
    /*!begin-code!*/
    Events.Emitter<Integer> ne = Events.emitter();
    ne.onEvent(x -> {
      squareSum[0] += x * x;
      ne.react(squareSum[0]);
    });
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-sum-ugly.html)!*/
  }

  @Test
  public void functionalSquareSum() {
    /*!begin-include!*/
    /*!begin-code!*/
    Events.Emitter<Integer> e = Events.emitter();
    Events<Integer> sum = e.map(x -> x * x).scanPast(0, (x, y) -> x + y);
    for (int i = 0; i < 5; i++) e.react(i);
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-sum-fun.html)!*/

    ArrayList<Integer> seen = new ArrayList();
    sum.onEvent(x -> seen.add(x));
    e.react(1);
    e.react(2);
    e.react(3);
    e.react(4);
    Assert.assertEquals(seen, new ArrayList<Integer>(Arrays.asList(1, 5, 14, 30)));
  }

  @Test
  public void filterAndUnion() {
    /*!begin-include!*/
    /*!begin-code!*/
    Events.Emitter<Integer> numbers = Events.emitter();
    Events<Integer> even = numbers.filter(x -> x % 2 == 0);
    Events<Integer> odd = numbers.filter(x -> x % 2 == 1);
    Events<Integer> numbersAgain = even.union(odd);
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-filter-union.html)!*/

    ArrayList<Integer> seen = new ArrayList();
    numbersAgain.onEvent(x -> seen.add(x));
    for (int i = 0; i < 10; i++) numbers.react(i);
    Assert.assertEquals(seen,
      new ArrayList<Integer>(Arrays.asList(0, 1, 2, 3, 4, 5, 6, 7, 8, 9)));
  }

  @Test
  public void muxAndUnion() {
    /*!begin-include!*/
    /*!begin-code!*/
    ArrayList<Integer> seen = new ArrayList();
    Events.Emitter<Events<Integer>> higherOrder = Events.emitter();
    Events.Emitter<Integer> evens = Events.emitter();
    Events.Emitter<Integer> odds = Events.emitter();
    Events.toMux(higherOrder).onEvent(x -> seen.add(x));

    evens.react(2);
    odds.react(1);
    higherOrder.react(evens);
    Assert.assertEquals(new ArrayList(Arrays.asList()), seen);
    odds.react(3);
    evens.react(4);
    Assert.assertEquals(new ArrayList(Arrays.asList(4)), seen);
    higherOrder.react(odds);
    evens.react(6);
    odds.react(5);
    Assert.assertEquals(new ArrayList(Arrays.asList(4, 5)), seen);
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-mux.html)!*/

    /*!begin-include!*/
    /*!begin-code!*/
    ArrayList<Integer> seen2 = new ArrayList();
    Events.Emitter<Events<Integer>> higherOrder2 = Events.emitter();
    Events.toUnion(higherOrder2).onEvent(x -> seen2.add(x));

    higherOrder2.react(evens);
    odds.react(3);
    evens.react(4);
    Assert.assertEquals(new ArrayList(Arrays.asList(4)), seen2);
    higherOrder2.react(odds);
    evens.react(6);
    Assert.assertEquals(new ArrayList(Arrays.asList(4, 6)), seen2);
    odds.react(5);
    Assert.assertEquals(new ArrayList(Arrays.asList(4, 6, 5)), seen2);
    /*!end-code!*/
    /*!end-include(reactors-java-event-streams-union.html)!*/
  }

  @Test
  public void take() {
    ArrayList<Integer> seen = new ArrayList();
    Events.Emitter<Integer> e = Events.emitter();
    e.take(1).onEvent(x -> seen.add(x));

    e.react(1);
    e.react(2);
    e.react(3);
    Assert.assertEquals(new ArrayList(Arrays.asList(1)), seen);
  }

  @Test
  public void drop() {
    ArrayList<Integer> seen = new ArrayList();
    Events.Emitter<Integer> e = Events.emitter();
    e.drop(3).onEvent(x -> seen.add(x));

    e.react(1);
    e.react(2);
    e.react(3);
    e.react(4);
    e.react(5);
    Assert.assertEquals(new ArrayList(Arrays.asList(4, 5)), seen);
  }
}
