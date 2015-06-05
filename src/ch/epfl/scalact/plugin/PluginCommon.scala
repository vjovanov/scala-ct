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

    def meetOrJoin(bt: String): (BT, String) = {
      val (lhs, rest) = apply0(bt)
      if (rest.startsWith(" ^ ")) {
        val (rhs, ret) = apply0(rest.substring(3, rest.length))
        (Meet(lhs, rhs), ret)
      } else if (rest.startsWith(" v ")) {
        val (rhs, ret) = apply0(rest.substring(3, rest.length))
        (Join(lhs, rhs), ret)
      } else throw new RuntimeException("Parsing error!" + bt)
    }

    def apply(bt: String): BT = apply0(bt)._1

    def apply0(bt: String): (BT, String) = {
      if (bt.startsWith("(")) {
        val (res, rest) = meetOrJoin(bt.substring(1))
        if (rest.head != ')') throw new RuntimeException("Parsing error!")
        (res, rest.substring(1))

      } else if (bt.startsWith("`rt")) (BTConst(rt), bt.substring("`rt".length))
      else if (bt.startsWith("`ct")) (BTConst(ct), bt.substring("`ct".length))
      else {
        val (i, j) = (bt.indexOf(' '), bt.indexOf(')'))
        if (i < 0 && j < 0) (BTVar(bt), "")
        else {
          val cutAt = if ((i * j) > 0) math.min(i, j) else math.max(i, j)
          (BTVar(bt.substring(0, cutAt)), bt.substring(cutAt))
        }
      }
    }
  }

  trait BT {
    def simplify: BT
    def substitute(vars: Map[String, BT]): BT
    def solve(vars: Map[String, BT] = Map.empty): BT = substitute(vars).simplify
  }
  final case class BTVar(name: String) extends BT {
    override def toString: String = name
    def simplify: BT = throw new RuntimeException(s"Variable $this is not substituted!")
    def substitute(vars: Map[String, BT]): BT =
      vars.getOrElse(name, this)
  }
  final case class BTConst(bt: Type) extends BT {
    override def toString: String = bt match {
      case `ct` => "`ct"
      case `rt` => "`rt"
    }
    def simplify: BT = this
    def substitute(vars: Map[String, BT]): BT = this
  }
  final case class Meet(bt1: BT, bt2: BT) extends BT {
    override def toString: String = s"($bt1 ^ $bt2)"

    def substitute(vars: Map[String, BT]): BT =
      Meet(bt1.substitute(vars), bt2.substitute(vars)).simplify

    override def simplify: BT = this match {
      case Meet(BTConst(c1), BTConst(c2))        => BTConst(glb(c1 :: c2 :: Nil))
      case Meet(lhs, `top`)                      => lhs.simplify
      case Meet(`top`, rhs)                      => rhs.simplify
      case Meet(lhs, `bot`)                      => BTConst(bot)
      case Meet(`bot`, rhs)                      => BTConst(bot)
      case Meet(lhs, rhs) if lhs == rhs          => lhs // idempotency
      case a Meet (b Join c) if a == b || a == c => a // absorption
    }
  }
  final case class Join(bt1: BT, bt2: BT) extends BT {
    override def toString: String = s"($bt1 v $bt2)"
    def substitute(vars: Map[String, BT]): BT =
      Join(bt1.substitute(vars), bt2.substitute(vars))

    override def simplify: BT = this match {
      case Join(BTConst(c1), BTConst(c2))        => BTConst(lub(c1 :: c2 :: Nil))
      case Join(lhs, `top`)                      => BTConst(top)
      case Join(`top`, rhs)                      => BTConst(top)
      case Join(lhs, `bot`)                      => lhs.simplify
      case Join(`bot`, rhs)                      => rhs.simplify
      case Join(lhs, rhs) if lhs == rhs          => lhs // idempotency
      case a Join (b Meet c) if a == b || a == c => a.simplify // absorption
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
