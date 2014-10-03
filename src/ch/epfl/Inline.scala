package ch.epfl.inline

import scala.annotation.StaticAnnotation
import language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.reflect.interpreter._

/** Annotation for carrying the body of the macro annotation. */
final class body[T](body: T) extends StaticAnnotation

object MacroUID {
  def impl(c: Context)(base: c.Expr[Long], exp: c.Expr[Long]): c.Expr[Long] = {
    // TODO: check if the input parameter is static and abort if not
    import c.universe._
    val bodyAnnotation =
      c.macroApplication.symbol.annotations.filter(_.tree.tpe <:< c.typeOf[body[_]]).head
    val body = bodyAnnotation.scalaArgs.head
    // replace all the arguments in the body with base and exp
    val Block(List(DefDef(_, _, _, _, _, f)), _) = body
    println(showCode(f))
    c.Expr[Long](f)
  }
}

object InlineMacros {
  // Just takes the body of the valdef from the annotation.
  def valImpl[T](c: Context): c.Expr[T] = {
    import c.universe._
    val bodyAnnotation =
      c.macroApplication.symbol.annotations.filter(_.tree.tpe <:< c.typeOf[body[_]]).head
    val body = bodyAnnotation.scalaArgs.head
    c.Expr[T](body)
  }

  // For now no type parameters
  //  def defImpl(c: Context): c.Expr[T] = {
  //    import c.universe._
  //    val bodyAnnotation =
  //      c.macroApplication.symbol.annotations.filter(_.tree.tpe <:< c.typeOf[body[_]]).head
  //    val Function(_, body) = bodyAnnotation.scalaArgs.head
  //    c.Expr[T](body)
  //  }

  def sinline[T](c: Context)(body: c.Expr[T]): c.Expr[T] = {
    import c.universe._
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
    c.Expr[T](res)
  }

  def treeString[T](c: Context)(body: c.Expr[T]): c.Expr[String] = {
    import c.universe._
    c.Expr[String](q"${showRaw(body.tree)}")
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
        List(q"""
          @body[${vd.tpt}](${vd.rhs})
          def x: ${vd.tpt} = macro ch.epfl.inline.InlineMacros.valImpl[${vd.tpt}]
        """)
      case (vd: ValDef) :: (body: DefDef) :: Nil =>
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

        List(q"""
          @body[Unit]({$body})
          def pow(base: Long, exp: Long): Long = macro ch.epfl.inline.MacroUID.impl
        """)
      case _ =>
        inputs
    }

    c.Expr[Any](Block(outputs, Literal(Constant(()))))
  }
}
