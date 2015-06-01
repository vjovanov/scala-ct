package ch.epfl.scalact.plugin

import scala.tools.nsc.Global

trait PluginCommon {
  val global: Global
  import global._
  case class TypeVariant(tpe: Type)
  case class Self(v: Tree)

  val (ct, ctstatic, static, dynamic) =
    (typeOf[ch.epfl.scalact.ct],
      typeOf[ch.epfl.scalact.ctstatic],
      typeOf[ch.epfl.scalact.static],
      typeOf[ch.epfl.scalact.dynamic])
  val variants = Set(ct, ctstatic, static, dynamic)

  object Variant {
    def unapply(x: Any): Option[(Type, Type)] = x match {
      case t: Tree if t.attachments.contains[TypeVariant] => unapply(t.attachments.get[TypeVariant].get.tpe)
      case AnnotatedType(List(Annotation(tpe, _, _), _*), t) if variants.exists(_ =:= tpe) => Some(t, tpe)
      case t: Type => Some(t, dynamic)
      case t: Tree => Some(t.tpe, dynamic)
    }
  }

  def variant(tree: Any): Type = tree match {
    case Variant(_, y) => y
  }

  /*
   * Convenience method for traversing annotated types.
   */
  def mapType(tpe: Type, f: (Type, Type) => Type): Type = tpe.widen match {
    case TypeRef(prefix, tp, args) if tp.isTypeParameter => // TODO find a better way
      TypeRef(prefix, tp, args)

    case TypeRef(prefix, tp, args) =>
      AnnotatedType(List(AnnotationInfo(f(dynamic, tpe), Nil, Nil)), TypeRef(prefix, tp, args.map(mapType(_, f))))

    case AnnotatedType(List(Annotation(annTpe, _, _), _*), TypeRef(prefix, tp, args)) if variants.exists(_ =:= annTpe) =>
      AnnotatedType(List(AnnotationInfo(f(annTpe, tpe), Nil, Nil)), TypeRef(prefix, tp, args.map(mapType(_, f))))

    case MethodType(l, resTp) => // TODO not sure about this
      AnnotatedType(List(AnnotationInfo(f(dynamic, tpe), Nil, Nil)), MethodType(l, mapType(resTp, f)))

    case NullaryMethodType(_) => // TODO do not know how to handle this
      tpe.widen

    case PolyType(vars, tpe) =>
      AnnotatedType(List(AnnotationInfo(f(dynamic, tpe), Nil, Nil)), PolyType(vars, mapType(tpe, f)))

    case _ => throw new RuntimeException("Unexpected Type " + showRaw(tpe))
  }

  def promoteType(tpe: Type, to: Type): Type = mapType(tpe, (_, tpe) => to)

  def promoteOne(tpe: Type, to: Type): Type =
    AnnotatedType(List(AnnotationInfo(to, Nil, Nil)), tpe)

  object MultipleApply {
    def unapply(value: Tree): Option[(Tree, List[Tree])] = value match {
      case Apply(x, y) =>
        Some(x match {
          case MultipleApply(rx, ry) =>
            (rx, ry ::: y)
          case _ =>
            (x, y)
        })
      case _ => None
    }
  }

  sealed trait DebugContext
  case object Default extends DebugContext
  case object AppTpe extends DebugContext
  case object Interpreter extends DebugContext
  case object ValDefs extends DebugContext
  case object IfStatement extends DebugContext
  case object Idents extends DebugContext
  case object SelectContext extends DebugContext
  case object News extends DebugContext
  case object Blocks extends DebugContext
  case object Inlining extends DebugContext
  case object Minimization extends DebugContext
  case object TypeChecking extends DebugContext

  var ident = 0
  def withIdent[T](i: Int)(b: => T): T = {
    ident += i
    val res = b
    ident -= 1
    res
  }

  var debugging = false
  val debugContexts: Set[DebugContext] = Set(Minimization)
  def debug(msg: String, context: DebugContext = Default): Unit =
    if (debugContexts.contains(context) && debugging) println("" * ident + msg)

}
