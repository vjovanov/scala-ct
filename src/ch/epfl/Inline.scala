package ch.epfl.inline

import scala.annotation.StaticAnnotation
import language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.reflect.interpreter._

/** Annotation for carrying the body of the macro annotation. */
final class body[T](body: T) extends StaticAnnotation

object MacroUID {
  def impl(c: Context)(base: c.Expr[Long], exp: c.Expr[Long]): c.Expr[Long] = {
    println("Call to: pow!")
    val global = c.universe.asInstanceOf[tools.nsc.Global]
    import c.universe._

    def inlineValTree(name: String, body: Tree): Tree = q"""
      @body($body)
      def ${newTermName(name)}: Any = macro ch.epfl.inline.InlineMacros.valImpl
    """

    val bodyAnnotation =
      c.macroApplication.symbol.annotations.filter(_.tree.tpe <:< c.typeOf[body[_]]).head

    val body = bodyAnnotation.scalaArgs.head

    // replace all the arguments in the body with base and exp
    val Block(List(DefDef(_, _, _, _, _, f)), _) = SinlineTransformerPH.transform(body)
    val res = Block(List(
      inlineValTree("exp", exp.tree),
      q"val base = ${base.tree}"),
      f)

    c.Expr[Long](c.untypecheck(res))
  }
}

object InlineMacros {
  // Just takes the body of the valdef from the annotation.
  def valImpl(c: reflect.macros.whitebox.Context): c.Expr[Any] = {
    import c.universe._
    val bodyAnnotation =
      c.macroApplication.symbol.annotations.filter(_.tree.tpe <:< c.typeOf[body[_]]).head
    val body = bodyAnnotation.scalaArgs.head
    c.Expr[Any](body)
  }

  def sinline[T](c: Context)(body: c.Expr[T]): c.Expr[T] = {
    import c.universe._
    println("Call to: Inline!")
    def static(tree: c.Tree): Boolean = {
      // there are no captured identifiers
      true
    }

    val tp = body.tree.tpe
    // check and interpret
    val res = body.tree match {
      case If(cond, t, e) if static(cond) =>
        if (interpret(c)(cond).asInstanceOf[Boolean]) t else e
      case If(cond, t, e) => c.abort(body.tree.pos,
        "sinline[T](body: T) can be used only with if statements where all identifiers in the condition are static.")
      case _ => c.abort(body.tree.pos,
        "@sinline can be used only with if statements.")
    }

    object SinlineTransformerPH extends Transformer {
      var allowMacros = true
      override def transform(tree: Tree): Tree = tree match {
        case _ =>
          if (allowMacros) {
            val global = c.universe.asInstanceOf[tools.nsc.Global]
            val noMacros = global.analyzer.unsuppressMacroExpansion(tree.asInstanceOf[global.Tree]).asInstanceOf[c.universe.Tree]
            super.transform(noMacros)
          } else super.transform(tree)
      }
    }
    import org.scalamacros.resetallattrs._
    val finalRes = c.resetAllAttrs(SinlineTransformerPH.transform(res))
    c.Expr[T](finalRes)
  }

  def treeString[T](c: Context)(body: c.Expr[T]): c.Expr[String] = {
    import c.universe._
    c.Expr[String](q"${showRaw(body.tree)}")
  }
}

object Utils {
  def setMacroExpansion(c: Context)(tree: c.Tree, enable: Boolean): c.Tree = {
    import c.universe._
    object SinlineTransformerPH extends Transformer {
      var allowMacros = enable
      def setMacroExpansion(tree: Tree, allowMacros: Boolean): Tree =
        if (allowMacros)
          global.analyzer.unsuppressMacroExpansion(tree.asInstanceOf[global.Tree]).asInstanceOf[c.universe.Tree]
        else
          global.analyzer.suppressMacroExpansion(tree.asInstanceOf[global.Tree]).asInstanceOf[c.universe.Tree]

      override def transform(tree: Tree): Tree = tree match {
        case Apply(TypeApply(Select(from, TermName("sinline")), targs), args) if allowMacros =>
          allowMacros = !allowMacros
          val res = args.map(transform(_))
          allowMacros = !allowMacros
          Apply(TypeApply(Select(from, TermName("sinline")), targs), res)
        case _ =>
          super.transform(tree)
      }
    }
  }

  def resetIdents(c: Context)(tree: c.Tree): c.Tree = {
    import c.universe._
    object TransformIdents extends Transformer {
      override def transform(tree: Tree): Tree = tree match {
        case Ident(TermName(nme)) =>
          Ident(newTermName(nme))
        case _ =>
          super.transform(tree)
      }
    }
    TransformIdents.transform(tree)
  }

  def inlineValTree(c: Context)(name: String, rhs: c.Tree): c.Tree = {
    import c.universe._
    q"""
      @body($rhs)
      def ${newTermName(name)}: Any = macro ch.epfl.inline.InlineMacros.valImpl
    """
  }

}

/** Companion object implementing @sinline macro annotation. */
private object InlineMacroAnnotation {

  def impl(c: Context)(annottees: c.Expr[Any]*): c.Expr[Any] = {
    import c.universe._
    val inputs = annottees.map(_.tree).toList
    val outputs = inputs match {
      case (vd: ValDef) :: Nil if vd.mods.hasFlag(Flag.LAZY) =>
        c.abort(vd.pos, "@sinline can not be applied to lazy vals.")
      case (vd: ValDef) :: Nil if vd.mods.hasFlag(Flag.MUTABLE) =>
        c.abort(vd.pos, "@sinline can not be applied to vars.")
      case (vd: ValDef) :: Nil =>
        List(inlineValTree(vd.name.toString, vd.rhs))
      case (vd: ValDef) :: (body: DefDef) :: Nil =>
        // TODO make sure it is not a class parameter
        /* HUMONGUOUS HACK ALERT!
         * Since macros must be separately compiled and must match the signature
         * of the method we just:
         * 1) generate trees for our macro
         * 2) generate code out of these trees
         * 3) compile this code with a separate ScalaCompiler
         * 4) load the output .class files
         * 5) use them in our method result
         * As easy as 1-2-3-4-5.
        */
        object SinlineTransformer extends Transformer {
          override def transform(tree: Tree): Tree = tree match {
            case _ =>
              val global = c.universe.asInstanceOf[tools.nsc.Global]
              // no macros tree
              val noMacros = global.analyzer.suppressMacroExpansion(tree.asInstanceOf[global.Tree]).asInstanceOf[c.universe.Tree]
              super.transform(noMacros)
          }
        }
        val noSInlineBody = SinlineTransformer.transform(body)
        val res = q"""
          @body[Unit]({$noSInlineBody})
          def pow(base: Long, exp: Long): Long = macro ch.epfl.inline.MacroUID.impl
        """
        List(res)
      case _ =>
        inputs
    }

    c.Expr[Any](Block(outputs, Literal(Constant(()))))
  }
}
