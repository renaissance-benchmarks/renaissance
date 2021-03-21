package io.reactors
package remote
package macros



import io.reactors.marshal.Marshalable
import scala.language.experimental.macros
import scala.reflect.macros.whitebox.Context



private[reactors] class Synthesizer(val c: Context) {
  import c.universe._

  def synthesizeSend(x: Tree): Tree = {
    val receiver: Tree = c.macroApplication match {
      case q"$qual.this.`package`.ChannelOps[$_]($receiver).!($_)" =>
        receiver
      case tree =>
        c.error(tree.pos, s"Send must have the form: <channel> ! <event>, got: $tree")
        q"null"
    }
    val receiverBinding = TermName(c.freshName("channel"))
    val threadBinding = TermName(c.freshName("thread"))
    val eventBinding = TermName(c.freshName("event"))
    val dataBinding = TermName(c.freshName("data"))

    // println("------")
    // println(x.tpe)
    // for (m <- x.tpe.members) {
    //   println(m, m.isMethod, m.isTerm, m.isPrivate, m.isPublic)
    // }
    // x.tpe.baseClasses.foreach { cls =>
    //   println(cls, cls.isJava, cls.info.decls)
    // }

    val sendTree = q"""
      val $receiverBinding = $receiver
      val $eventBinding = $x
      val $threadBinding = _root_.io.reactors.Reactor.currentReactorThread
      if ($threadBinding != null && $threadBinding.dataBuffer != null) {
        val $dataBinding = $threadBinding.dataBuffer
        ${genMarshal(x.tpe, q"$eventBinding", q"$dataBinding")}
      } else {
        $receiverBinding.send($eventBinding)
      }
    """
    // println(sendTree)
    sendTree
  }

  def findDynamicSuperclass(klass: Type): Option[Type] = {
    val firstJavaAncestor = klass.baseClasses.filter(!_.asClass.isTrait).find { pred =>
      pred.isJava
    }.map(_.asType.toType)
    firstJavaAncestor
  }

  def genMarshal(klass: Type, x: Tree, data: Tree): Tree = {
    if (klass <:< typeOf[Marshalable]) {
      q"$x.marshal($data)"
    } else {
      val staticPart = q"???"
      val dynamicPart = findDynamicSuperclass(klass) match {
        case Some(s) => q"""
          _root_.io.reactors.remote.RuntimeMarshaler.marshalAs(
            classOf[$s], $x, $data, false)
        """
        case None => q"()"
      }
      if (klass.typeSymbol.asClass.isFinal) {
        q"""
          $staticPart
          $dynamicPart
        """
      } else {
        q"""
          if ($x.getClass ne classOf[${klass}]) {
            if ($x.isInstanceOf[_root_.io.reactors.marshal.Marshalable]) {
              $x.asInstanceOf[_root_.io.reactors.marshal.Marshalable].marshal($data)
            } else {
              _root_.io.reactors.remote.RuntimeMarshaler.marshal($x, $data)
            }
          } else {
            $staticPart
            $dynamicPart
          }
        """
      }
    }
  }

  def genUnmarshal(klass: Class[_], data: Tree): Tree = {
    ???
  }
}
