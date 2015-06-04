package ch.epfl.scalact.plugin

import ch.epfl.scalact._

import scala.annotation.StaticAnnotation
import scala.tools.nsc.Global

trait PluginCommon {
  val global: Global
  import global._
  case class TypeVariant(tpe: Type)
  case class Self(v: Tree)

  val (rt, ct) = (typeOf[ch.epfl.scalact.rt], typeOf[ch.epfl.scalact.ct])
  val (bot, top) = (ct, rt)
  // TODO eliminate
  val static = typeOf[ch.epfl.scalact.static]
  val variants = Set(ct, static, rt)

  object BT extends StaticAnnotation {
    def apply(bt: String): BT = {
      val terms = bt.split("").map(parseTerm)
      terms.tail.foldLeft[BT](terms.head)((agg, v) => Meet(agg, v))
    }

    private final def parseTerm(t: String) = t match {
      case "ct" => BTConst(ct)
      case "rt" => BTConst(rt)
      case x    => BTVar(x)
    }
  }

  trait BT {
    def simplify: BT
    def substitute(vars: Map[String, Type]): BT
    def solve(vars: Map[String, Type] = Map.empty): BT = substitute(vars).simplify
  }
  final case class BTVar(name: String) extends BT {
    override def toString: String = name
    def simplify: BT = throw new RuntimeException(s"Variable $this is not substituted!")
    def substitute(vars: Map[String, Type]): BT =
      vars.get(name).map(BTConst).getOrElse(this)
  }
  final case class BTConst(bt: Type) extends BT {
    override def toString: String = bt match {
      case `ct` => "`ct"
      case `rt` => "`rt"
    }
    def simplify: BT = this
    def substitute(vars: Map[String, Type]): BT = this
  }
  final case class Meet(bt1: BT, bt2: BT) extends BT {
    override def toString: String = s"$bt1 & $bt2"

    def substitute(vars: Map[String, Type]): BT =
      Meet(bt1.substitute(vars), bt2.substitute(vars))

    override def simplify: BT = this match {
      case Meet(BTConst(c1), BTConst(c2)) => BTConst(lub(c1 :: c2 :: Nil))
    }
  }
  final case class Join(bt1: BT, bt2: BT) extends BT {
    override def toString: String = s"$bt1 | $bt2"
    def substitute(vars: Map[String, Type]): BT =
      Join(bt1.substitute(vars), bt2.substitute(vars))

    override def simplify: BT = this match {
      case Join(BTConst(c1), BTConst(c2)) => BTConst(glb(c1 :: c2 :: Nil))
    }
  }

  object Variant {
    def unapply(x: Any): Option[(Type, Type)] = x match {
      case t: Tree if t.attachments.contains[TypeVariant] => unapply(t.attachments.get[TypeVariant].get.tpe)

      case AnnotatedType(l, t) if l.exists(ann => variants.exists(_ =:= ann.atp)) =>
        val tpe = l.find(ann => variants.exists(_ =:= ann.atp)).head.atp
        Some(t, tpe)

      case t: Type => Some(t, rt)
      case t: Tree => Some(t.tpe, rt)
    }
  }

  def variant(tree: Any): Type = tree match {
    case Variant(_, y) => y
  }

  def functionAnnotation(methodSym: Symbol): Type = {
    val allVariants = methodSym.annotations.filter(_.tree.tpe <:< typeOf[ch.epfl.scalact.Variant])
    if (allVariants.size > 1) error("Function should have only one ct argument.")
    allVariants.headOption.map(_.tree.tpe).getOrElse(rt)
  }

  def btAnnotation(methodSym: Symbol): BT = {
    val allBT = methodSym.annotations.filter(_.tree.tpe <:< typeOf[ch.epfl.scalact.BT])
    if (allBT.size > 1) error("Function should have one BT annotation.")
    allBT.headOption.map(_.tree).map { case Literal(Constant(c: String)) => BT(c) }.get
  }
  def userAugmented(constraints: BT, annTpe: Type) = annTpe match {
    case `ct` => Join(constraints, BTConst(ct))
    case `rt` => Meet(constraints, BTConst(rt))
  }

  /*
   * Convenience method for traversing annotated types.
   */
  def mapType(tpe: Type, f: (Type, Type) => Type): Type = tpe.widen match {
    case TypeRef(prefix, tp, args) if tp.isTypeParameter => // TODO find a better way
      TypeRef(prefix, tp, args)

    case TypeRef(prefix, tp, args) =>
      AnnotatedType(List(AnnotationInfo(f(rt, tpe), Nil, Nil)), TypeRef(prefix, tp, args.map(mapType(_, f))))

    case AnnotatedType(l, TypeRef(prefix, tp, args)) if l.exists(ann => variants.exists(_ =:= ann.atp)) =>
      val annList = l.filter(ann => variants.exists(_ =:= ann.atp))
      val annTpe = annList.head.atp

      AnnotatedType(
        AnnotationInfo(f(annTpe, tpe), Nil, Nil) :: (l diff annList),
        TypeRef(prefix, tp, args.map(mapType(_, f))))

    case MethodType(l, resTp) => // TODO not sure about this
      AnnotatedType(List(AnnotationInfo(f(rt, tpe), Nil, Nil)), MethodType(l, mapType(resTp, f)))

    case NullaryMethodType(_) => // TODO do not know how to handle this
      tpe.widen

    case PolyType(vars, tpe) =>
      AnnotatedType(List(AnnotationInfo(f(rt, tpe), Nil, Nil)), PolyType(vars, mapType(tpe, f)))

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

  var debugging = true
  val debugContexts: Set[DebugContext] = Set(TypeChecking)
  def debug(msg: String, context: DebugContext = Default): Unit =
    if (debugContexts.contains(context) && debugging) println("" * ident + msg)

}
