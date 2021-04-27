package io.reactors.japi;



import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;
import scala.*;
import scala.reflect.*;
import scala.runtime.*;



class Util {
  public static <T> io.reactors.Arrayable<T> arrayable() {
    ClassTag<T> tag = ClassTag$.MODULE$.apply(Object.class);
    io.reactors.Arrayable<T> a = io.reactors.Arrayable$.MODULE$.ref(tag);
    return a;
  }

  public static <T> AbstractFunction0<BoxedUnit> toScalaFunction(Runnable r) {
    return new AbstractFunction0<BoxedUnit>() {
      public BoxedUnit apply() {
        r.run();
        return BoxedUnit.UNIT;
      }
    };
  }

  public static <T> AbstractFunction1<T, BoxedUnit> toScalaFunction(Consumer<T> c) {
    return new AbstractFunction1<T, BoxedUnit>() {
      public BoxedUnit apply(T x) {
        c.accept(x);
        return BoxedUnit.UNIT;
      }
    };
  }

  public static <T> AbstractFunction1<T, Object> toScalaFunction(
    Predicate<T> p
  ) {
    return new AbstractFunction1<T, Object>() {
      public Object apply(T x) {
        return p.test(x);
      }
    };
  }

  public static <T, R> AbstractFunction1<T, R> toScalaFunction(Function<T, R> c) {
    return new AbstractFunction1<T, R>() {
      public R apply(T x) {
        return c.apply(x);
      }
    };
  }

  public static <T> PartialFunction<T, BoxedUnit> toScalaPartialFunction(
    Consumer<T> c
  ) {
    return new AbstractPartialFunction<T, BoxedUnit>() {
      public BoxedUnit apply(T x) {
        c.accept(x);
        return BoxedUnit.UNIT;
      }
      public boolean isDefinedAt(T x) {
        return true;
      }
    };
  }

  public static <T1, T2, R> AbstractFunction2<T1, T2, R> toScalaFunction(
    BiFunction<T1, T2, R> c
  ) {
    return new AbstractFunction2<T1, T2, R>() {
      public R apply(T1 x1, T2 x2) {
        return c.apply(x1, x2);
      }
    };
  }
}
