package io.reactors
package marshal






class ClassDescriptor(
  val klazz: Class[_],
  val fields: Array[Platform.Reflect.FieldDescriptor]
)
