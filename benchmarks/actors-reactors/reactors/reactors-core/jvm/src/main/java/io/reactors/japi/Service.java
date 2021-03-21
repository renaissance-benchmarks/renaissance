package io.reactors.japi;



import scala.reflect.ClassTag;
import scala.reflect.ClassTag$;



public interface Service {
  default <S extends io.reactors.Protocol.Service> S getRawService(
    ReactorSystem system, Class<S> cls
  ) {
    ClassTag<S> tag = ClassTag$.MODULE$.<S>apply(cls);
    return system.rawSystem().<S>service(tag);
  }
}
