package ch.epfl.scalact.plugin

import ch.epfl.scalact.Variant

import scala.reflect.macros.blackbox.Context
import scala.tools.nsc
import nsc.Global
import nsc.transform.{ Transform, TypingTransformers }
import nsc.plugins.Plugin
import nsc.plugins.PluginComponent
import scala.collection.mutable
import scala.reflect.interpreter._

class PartialEvaluationPlugin(val global: Global) extends Plugin with PluginCommon {
  import global._

  val name = "partial-evaluation"
  val description = "Partially evaluates Scala trees according to the type annotations."
  val components = List[PluginComponent](BTTyper, Component)

  /**
   * Performs binding time analysis and coercion.
   */
  private object BTTyper extends PluginComponent with TypingTransformers with Transform {
    val global: PartialEvaluationPlugin.this.global.type = PartialEvaluationPlugin.this.global
    val runsAfter = List[String]("typer")
    val phaseName = "bt-typer"
    def newTransformer(unit: CompilationUnit) = new BTTyperTransformer(unit)
    case class BTContext(constructor: Boolean, tparams: Set[Symbol], selfBT: Type)
    var ctx = BTContext(false, Set.empty, dynamic) // expected type
    def withCtx[T](newCtx: BTContext)(t: => T): T = {
      val oldCtx = ctx
      ctx = newCtx
      val res = t
      ctx = oldCtx
      res
    }

    class BTTyperTransformer(unit: CompilationUnit) extends TypingTransformer(unit) {
      override def transform(tree: Tree): Tree = withIdent(1) {
        val res = tree match {
          case pd @ PackageDef(refTree, body) => treeCopy.PackageDef(tree, refTree, body.map(transform))
          case Import(_, _)                   => tree

          case ClassDef(mods, name, tparams, tmpl) =>
            treeCopy.ClassDef(tree, mods, name, tparams, withCtx(ctx.copy(constructor = true, tparams = ctx.tparams ++ tparams.map(_.symbol))) { transformTemplate(tmpl) })

          case ModuleDef(mods, name, tmpl)   => treeCopy.ModuleDef(tree, mods, name, transformTemplate(tmpl))
          case Template(parents, self, body) => treeCopy.Template(tree, parents.map(transform), transformValDef(self), body.map(transform))
          case Select(qual, name)            => treeCopy.Select(tree, transform(qual), name)
          case Ident(i)                      => treeCopy.Ident(tree, i)
          case TypeTree()                    => treeCopy.TypeTree(tree)

          case DefDef(mods, name, tparams, vparamss, tpt, rhs) => // assume parameters if the type is not in the list!
            treeCopy.DefDef(tree, mods, name, tparams, vparamss, tpt, transform(rhs))

          case Block(stats, expr)                => treeCopy.Block(tree, stats.map(transform), transform(expr))
          case Apply(fun, args)                  => treeCopy.Apply(tree, transform(fun), args.map(transform))
          case Super(qual, mix)                  => treeCopy.Super(tree, transform(qual), mix)
          case This(qual)                        => treeCopy.This(tree, qual)
          case Literal(Constant(a))              => tree
          case ValDef(mods, name, tpt, rhs)      => treeCopy.ValDef(tree, mods, name, tpt, rhs)
          case If(cond, thenp, elsep)            => treeCopy.If(tree, transform(cond), transform(thenp), transform(elsep))
          case Throw(expr)                       => treeCopy.Throw(tree, expr)
          case TypeDef(mods, name, tparams, rhs) => treeCopy.TypeDef(tree, mods, name, tparams, transform(rhs))
          case New(tpt)                          => treeCopy.New(tree, tpt)
          case TypeApply(fun, args)              => treeCopy.TypeApply(tree, transform(fun), args)
          case Function(vparams, body)           => treeCopy.Function(tree, vparams, transform(body))
          case EmptyTree                         => tree
          case _                                 => ???
        }
        if (unit.body == tree) debug(s"$tree \n becomes \n $res", TypeChecking)
        res
      }
    }
  }

  private object Component extends PluginComponent with TypingTransformers with Transform {
    val global: PartialEvaluationPlugin.this.global.type = PartialEvaluationPlugin.this.global
    val runsAfter = List[String]("typer")
    val phaseName = PartialEvaluationPlugin.this.name
    def newTransformer(unit: CompilationUnit) = new PartialEvaluatorTransformer(unit)

    // here we make a macro context in order to use the Macro API
    val context = new {
      val universe: global.type = global
      val callsiteTyper: global.analyzer.Typer = global.typer
      val expandee = EmptyTree
    } with scala.reflect.macros.contexts.Context {
      val prefix = null
    }

    class PartialEvaluatorTransformer(unit: CompilationUnit)
      extends TypingTransformer(unit) {

      /**
       * Stores promoted types of trees that were encountered
       * during partial evaluation.
       */
      private val promotedTypes: mutable.Map[Symbol, (Tree, Type)] = mutable.HashMap.empty
      def isInline(t: Tree): Boolean = t match {
        case Variant(_, `ct`) => true
        case _                => false
      }

      def variantType(tree: Tree): Type = tree match {
        case t: Tree if t.attachments.contains[TypeVariant]  => t.attachments.get[TypeVariant].get.tpe
        case Ident(_) if promotedTypes.contains(tree.symbol) => variantType(promotedTypes(tree.symbol)._1)
        case Ident(_)                                        => promoteType(tree.tpe, dynamic)
        case _ =>
          debug(s"<warn> Have no variant for: $tree: ${tree.tpe}")
          tree.tpe
      }

      def value[T](t: Tree): T = {
        if (variant(t) =:= dynamic) throw new RuntimeException(s"Trying to fetch a value of the dynamic value: ${t}.")
        (t match {
          case t if t.attachments.contains[TreeValue] => t.attachments.get[TreeValue].get
          case Literal(Constant(x))                   => x
          case Ident(_)                               => value[T](promotedTypes(t.symbol)._1)
        }).asInstanceOf[T]
      }

      def ctPackageObject(t: Tree) = t.symbol.owner.isType &&
        t.symbol.owner.asType == typeOf[ch.epfl.scalact.`package`.type].typeSymbol

      def inlineTransformed[C <: Context](c: C)(body: c.Tree)(
        tr: (c.Tree, c.internal.TypingTransformApi) => c.Tree)(
          tparamsMap: Map[c.Symbol, c.Symbol])(paramss: List[List[c.Tree]], args: List[c.Tree]): c.Tree = {
        import c.universe._
        import c.universe.internal._, decorators._

        val params = paramss.flatten
        val paramsMap = (params zip args).map {
          case (param @ q"${ _ } val $name: ${ _ } = ${ _ }", arg) =>
            val temp = c.freshName(name)
            val tempSym = localTyper.context.owner.asInstanceOf[Symbol].newTermSymbol(temp)
            val newArg = c.typecheck(arg)
            tempSym.setInfo(newArg.tpe.widen)

            val valDef = c.internal.valDef(tempSym, c.internal.changeOwner(arg, c.internal.enclosingOwner, tempSym))
            (param.symbol, (tempSym, valDef))
        }.toMap

        // typecheck idents and replace type variables
        val inlinedBody = c.internal.typingTransform(body)((tree, api) => tree match {
          case i @ Ident(_) if paramsMap contains tree.symbol =>
            val sym = paramsMap(tree.symbol)._1
            api.typecheck(q"$sym")

          case TypeTree() =>
            val transformedTpe = tree.tpe.map {
              case TypeRef(prefix, tp, targs) if tparamsMap.contains(tp) =>
                c.universe.internal.typeRef(prefix, tparamsMap(tp), targs)
              case tp => tp
            }
            TypeTree(transformedTpe)
          case _ =>
            api.default(tree)
        })

        val res = q"""{
          ..${paramsMap.values.map(_._2)}
          ${c.internal.typingTransform(inlinedBody)(tr)}
        }"""
        debug("Inlined: " + showCode(res), Inlining)
        res
      }

      def inlineMethod(c: Context)(f: c.Tree, self: c.Tree)(targs: List[c.Type])(args: List[c.Tree]): c.Tree = {
        import c.universe._
        import c.universe.internal._, decorators._
        val q"${ _ } def ${ _ }[..$tparams](...$paramss): $tpe = $body" = f
        val tpMap = (tparams zip targs).map(x => (x._1.symbol, x._2.typeSymbol)).toMap
        inlineTransformed[c.type](c)(body)((tree, api) => tree match {
          case This(_) => self
          case _       => api.default(tree)
        })(tpMap)(paramss, args)
      }

      def inlineLambda(c: Context)(f: c.Tree, args: List[c.Tree]): c.Tree = {
        import c.universe._
        import c.universe.internal._, decorators._
        val q"(..$params) => $body" = f
        inlineTransformed[c.type](c)(body)((tree, api) => api.default(tree))(Map())(List(params), args)
      }

      // creates a constant out of the value
      def const(t: Any): Tree =
        transform(localTyper.typed(Literal(Constant(t))))

      def inlineTree(valueOrTree: Any): Tree = valueOrTree match {
        case tree: Tree => tree
        case value      => const(value)
      }

      /*
       * All trees in the current run.
       */
      val allTrees: Seq[Tree] = global.currentRun.units.map(_.body).toSeq
      def eval(tree: Tree): Tree = {
        val (engine, (value, env)) = interpret.withDefs(context)(allTrees)(tree)
        val finalRes = if (tree.tpe <:< typeOf[scala.AnyVal]) {
          val (evalRes, _) = value.asInstanceOf[engine.JvmValue].reify(env.asInstanceOf[engine.Env])
          inlineTree(evalRes).updateAttachment(TypeVariant(promoteType(tree.tpe, ct)))
        } else
          tree.updateAttachment(TreeValue(value, Some(env), false))

        assert(variant(finalRes) == ct, s"Everything interpreted must be ct: culprit $tree.")
        finalRes
      }

      def functionAnnotation(methodSym: Symbol): Type = {
        val allVariants = methodSym.annotations.filter(_.tree.tpe <:< typeOf[ch.epfl.scalact.Variant])
        if (allVariants.size > 1) error("Function should have only one ct argument.")
        allVariants.headOption.map(_.tree.tpe).getOrElse(dynamic)
      }

      /*
       * Fetching sources.
       */
      def symSourceWithModuleClasses = global.currentRun.symSource.map(x => (if (x._1.isModule) x._1.moduleClass else x._1, x._2))

      def canInline(sym: Symbol): Boolean =
        sym.ownerChain.find(symSourceWithModuleClasses.contains(_)).nonEmpty ||
          sym.ownerChain.find(global.currentRun.symSource.contains(_)).nonEmpty ||
          sym.owner == typeOf[Function1[_, _]].typeSymbol || sym.owner == typeOf[Function2[_, _, _]].typeSymbol

      def fetchBody(sym: Symbol): Option[Tree] = {
        val classSym = sym.ownerChain.find(symSourceWithModuleClasses.contains(_)).orElse(
          sym.ownerChain.find(global.currentRun.symSource.contains(_)))
        classSym.flatMap { classSym =>
          val file = (if (global.currentRun.symSource.contains(classSym))
            global.currentRun.symSource
          else symSourceWithModuleClasses)(classSym)

          val unit = global.currentRun.units.find(_.source.file == file).get
          val method = unit.body.find {
            case df: DefDef => df.symbol == sym
            case _          => false
          }

          method
        }
      }

      def minimize(block: Tree): Tree = {
        debug("Minimizing:" + block, Minimization)
        val res = minimize(context)(block.asInstanceOf[context.Tree]).asInstanceOf[Tree]
        debug("Minimized:" + res, Minimization)
        res
      }

      def minimize(c: Context)(block: c.Tree): c.Tree = {
        import c.universe._
        import c.universe.internal._, decorators._

        val vals: mutable.Map[Symbol, c.Tree] = mutable.Map()
        val minimizedBody = c.internal.typingTransform(block) { (tree, api) =>
          tree match {
            case q"${ _ } val $valName: ${ _ } = $body" if (!tree.symbol.isParameter) =>
              val newBody = api.default(body)
              vals += (tree.symbol -> newBody)
              q"()"
            case Ident(x) if (vals.contains(tree.symbol)) =>
              vals(tree.symbol)
            case t if !t.attachments.get[Self].isEmpty =>
              val selfTree = t.attachments.get[Self].get.v.asInstanceOf[c.Tree]
              t.removeAttachment[Self]

              val res = api.default(t)
              val newSelf = Self(api.default(selfTree).asInstanceOf[global.Tree])
              res.updateAttachment(newSelf)
            case _ =>
              api.default(tree)
          }
        }
        def removeBlocks(body: Tree): Tree = body match {
          case Block(_, res) => removeBlocks(res)
          case _             => body
        }

        // get rid of the block
        val noBlocks = removeBlocks(minimizedBody)
        noBlocks.updateAttachment(Self(noBlocks.asInstanceOf[global.Tree]))
      }

      def application(sym: Symbol, tree: Tree, lhs: Tree, args: List[Tree]): Tree = {
        // Typechecking
        case class Constraint(tp: Type, level: Int)
        val tparams = sym.asMethod.typeParams.map(x => (x, mutable.Set[Constraint]())).toMap

        def compose(m1: Map[Symbol, Set[Constraint]], m2: Map[Symbol, Set[Constraint]]): Map[Symbol, Set[Constraint]] =
          (m1.keySet ++ m2.keySet).map(sym => (sym -> (m1.getOrElse(sym, Set()) ++ m2.getOrElse(sym, Set())))).toMap

        def params(expectedTp: Type, tp: Type): Map[Symbol, Set[Constraint]] = {
          (expectedTp, tp) match {
            case (Variant(TypeRef(_, ptp, pargs), variantE), Variant(TypeRef(_, _, args), variantA)) =>
              val constraints = (if (tparams.contains(ptp))
                Seq((ptp -> Set(Constraint(variant(tp), if (variantE != dynamic) 1 else 0))))
              else Seq()).toMap
              (pargs zip args).foldLeft(constraints)((agg, tps) => compose(agg, (params _).tupled(tps)))
          }
        }
        debug(s"------------------------------ ${sym.owner}.${sym.name} ---------------------------------")
        val constraints = (sym.asMethod.paramLists.flatten.map(_.tpe) zip args.map(variantType))
          .foldLeft(Map[Symbol, Set[Constraint]]())((agg, x) => compose(agg, (params _).tupled(x)))

        val minimizedConstraints: Map[Symbol, Type] = constraints mapValues { constraints =>
          val (hiPri, loPri) = constraints partition (_.level == 1)
          val relevantConstraints = if (hiPri.isEmpty) loPri else hiPri
          // TODO set rules in stone with Denys. Not sure what to do with inlineable.
          relevantConstraints.foldLeft(ct) { (agg, cons) => lub(agg :: cons.tp :: Nil) }
        }

        def typecheck(arg: Tree, expectedTp: Type, tp: Type): Unit = (expectedTp, tp) match {
          case (Variant(TypeRef(_, ptp, pargs), variantE), Variant(TypeRef(_, _, args), variantA)) =>
            val expectedVariant =
              if (minimizedConstraints.contains(ptp)) minimizedConstraints(ptp)
              else variantE

            if (expectedVariant <:< static && variantA =:= dynamic)
              warning(s"Argument $arg did not match inlinity expected: $expectedTp got: $tp.")

            (pargs zip args).foreach(tps => typecheck(arg, tps._1, tps._2))
        }

        def coaerce(expectedTp: Type, tp: Type): Type = (expectedTp, tp) match {
          case (Variant(TypeRef(_, ptp, pargs), variantE), Variant(TypeRef(prefix, tpe, args), variantA)) =>
            val expectedVariant =
              if (minimizedConstraints.contains(ptp)) minimizedConstraints(ptp)
              else variantE

            val newArgs = (pargs zip args).map(tps => (coaerce _).tupled(tps))
            if (!(variantA =:= dynamic) && expectedVariant <:< variantA)
              promoteOne(TypeRef(prefix, tpe, newArgs), expectedVariant)
            else if (expectedVariant =:= ctstatic && variantA =:= static)
              promoteOne(TypeRef(prefix, tpe, newArgs), ct)
            else promoteOne(TypeRef(prefix, tpe, newArgs), variantA)
        }

        val expectedTypes = sym.asMethod.paramLists.flatten.map { param =>
          if (isInline(lhs)) promoteType(param.tpe, ct)
          else param.tpe
        }

        val promoteArgs = (expectedTypes zip args).map {
          case (param, arg) =>
            debug(s"(Tree, Attachment) of param $param is ($arg, ${arg.attachments.get[TypeVariant]})", AppTpe)
            typecheck(arg, param, variantType(arg))
            // if all is OK coaerce arguments
            val resultType = coaerce(param, variantType(arg))
            arg.updateAttachment(TypeVariant(resultType))
        }

        val methodSym = lhs.attachments.get[Self].map(_.v).flatMap { x =>
          x.tpe.typeSymbol.typeSignature.member(sym.asMethod.name).alternatives.find(alt => alt.typeSignature matches sym.asMethod.infoIn(x.tpe))
        }.getOrElse(sym)

        val shouldInline = !sym.isConstructor &&
          (functionAnnotation(methodSym) =:= ct || // explicitly annotated
            // TODO Discuss with Denys what to do here... TODO Refine for nested types.
            (functionAnnotation(methodSym) =:= ctstatic && (expectedTypes zip args).forall(x => !(variant(x._1) =:= ctstatic) || variant(x._2) =:= ct)) || // function is ctstatic and all ctstatic args are satisfied
            isInline(lhs)) // lhs is promoted to inline (type checking checks the arguments)
        debug(s"Method body fetching: " + lhs.attachments.get[Self] + " " + methodSym.owner + " " + functionAnnotation(methodSym) + " " + lhs)
        def withInline[T](cond: Boolean)(block: => T): T = {
          if (cond) inlineLevel += 1
          val res = block
          if (cond) inlineLevel -= 1
          res
        }

        withInline(isInline(lhs) && !sym.isConstructor) {
          val res = if (shouldInline) {
            debug("Args before:" + args.map(arg => s"$arg: ${arg.tpe}"), AppTpe)
            debug("Args after:" + promoteArgs.map(arg => s"$arg: ${arg.attachments.get[TypeVariant].get.tpe}"), AppTpe)

            val res = if (canInline(sym)) { // method
              val self = lhs.attachments.get[Self].map(_.v).getOrElse(EmptyTree)

              // here we have a method sym
              val inlined = if (methodSym.owner == typeOf[Function1[_, _]].typeSymbol || methodSym.owner == typeOf[Function2[_, _, _]].typeSymbol) {
                val tmpLevel = inlineLevel
                inlineLevel = 0
                val inlined = inlineLambda(context)(self, promoteArgs)
                debug(s"Inlining ${sym.owner}.$sym: ${showCode(inlined)}", AppTpe)
                val res = transform(localTyper.typed(inlined))
                debug(s"Inlined ${sym.owner}.$sym: ${showCode(res)}: ${variantType(res)}", AppTpe)

                inlineLevel = tmpLevel
                res
              } else {
                val inlined = inlineMethod(context)(
                  fetchBody(methodSym).get.asInstanceOf[context.Tree], self.asInstanceOf[context.Tree])(
                    List(typeOf[Int], typeOf[Int]))(
                      promoteArgs.asInstanceOf[List[context.Tree]])

                debug(s"Inlining ${sym.owner}.$sym: ${showCode(inlined)}", AppTpe)
                val res = transform(localTyper.typed(inlined))
                debug(s"Inlined ${sym.owner}.$sym: ${showCode(res)}: ${variantType(res)}", AppTpe)
                res

              }
              // debug(s"Inlining ${sym.owner}.$sym: ${show(inlined)}", AppTpe)
              // val res = transform(localTyper.typed(inlined))
              // debug(s"Inlined ${sym.owner}.$sym: ${show(res)}: ${variantType(res)}", AppTpe)
              inlined
            } else { // interpretation of the unavailable functions
              val interpretee = treeCopy.Apply(tree, lhs, promoteArgs.map { arg =>
                val argTree = if (variant(arg) =:= ct) inlineTree(arg)
                else {
                  val res = localTyper.typed(q"()")
                  res.updateAttachment(TreeValue(arg, None, false))
                  res
                }
                // if the argument is a function with types that are dynamic
                if (global.definitions.isFunctionType(argTree.tpe) && argTree.tpe.typeArgs.forall(variant(_) == dynamic)) {
                  // make a callback from the interpreter
                  val callback: List[Tree] => Tree = args => {
                    transform(localTyper.typed(inlineLambda(context)(arg, args)))
                  }
                  argTree.updateAttachment(TreeValue(callback, None, false))
                }
                argTree
              })
              debug(s"Interpret: $interpretee", Interpreter)
              eval(interpretee)
            }

            def promote(returnType: Type, tpe: Type): Type = (returnType, tpe) match {
              case (Variant(TypeRef(_, etp, eargs), variantRTPE), Variant(TypeRef(prefix, tp, args), variant)) =>
                debug(s"Promoting $returnType to ${tpe}", ValDefs)
                // TODO resolve this issue when minimizedConstraints does not contain it
                val resultInlinity = if (etp.isTypeParameter && minimizedConstraints.contains(etp))
                  minimizedConstraints(etp)
                else variant
                val promotedType = tp
                // val promotedType = if (etp.isTypeParameter && tpMap.contains(tp.typeSymbol)) tpMap(tp)
                // else tp
                AnnotatedType(List(AnnotationInfo(resultInlinity, Nil, Nil)),
                  TypeRef(prefix, promotedType, (eargs zip args).map((promote _).tupled)))
            }

            // typing the return type
            val returnType = sym.asMethod.returnType
            debug(s"Return type: ${show(returnType)} promoting to ${variantType(res)}", Minimization)
            val minimizedRes = if (variant(res) =:= ct) minimize(res) else res
            minimizedRes.updateAttachment(TypeVariant(promote(returnType, variantType(res))))
          } else if (sym.isConstructor && isInline(lhs)) {
            val res = treeCopy.Apply(tree, lhs, promoteArgs)
            val returnType = sym.asMethod.returnType
            res.updateAttachment(TypeVariant(promoteType(returnType, ct)))
          } else if (!sym.isConstructor) {
            val res = treeCopy.Apply(tree, lhs, promoteArgs)
            res.updateAttachment(TypeVariant(promoteType(tree.tpe, dynamic)))
          } else {
            super.transform(tree)
          }

          res
        }
      }

      var inlineLevel: Int = 0
      def byMode(tp: Type) = if (inlineLevel == 0) tp else ct

      override def transform(tree: Tree): Tree = withIdent(0) {
        tree match {
          // TODO Gross Hack (we need access to underlying objects here or in the interpreter)
          case q"$x == $y" if y.tpe.toString == "library.Nil.type" =>
            if (x.tpe.toString == y.tpe.toString && y.tpe.toString == "library.Nil.type")
              transform(localTyper.typed(q"_root_.ch.epfl.scalact.ct(true)"))
            else transform(localTyper.typed(q"_root_.ch.epfl.scalact.ct(false)"))

          // constants and lambdas are static
          case Literal(Constant(x)) =>
            if (tree.attachments.get[TypeVariant].isEmpty) // do not delete inlinity
              // TODO remove the typecheck
              tree.updateAttachment(TypeVariant(promoteType(localTyper.typed(tree).tpe.widen, byMode(static))))

            tree.updateAttachment(Self(tree))

          case Function(vparams, body) =>
            val res = treeCopy.Function(tree, vparams.map(x => transform(x).asInstanceOf[ValDef]), body)
            res.updateAttachment(TypeVariant(promoteOne(tree.tpe, byMode(static))))
            res.updateAttachment(Self(res))
            res

          case New(sel) =>
            val newSel = transform(sel)
            val bindingTime = if (variant(tree.tpe) =:= ct) ct else byMode(static)
            debug(s"New(sel: ${variant(newSel)}): ${promoteOne(tree.tpe, bindingTime)}", News)
            treeCopy.New(tree, newSel).updateAttachment(TypeVariant(promoteOne(tree.tpe, bindingTime)))

          case Block(body, res) =>
            debug("Block: " + show(res), Blocks)
            val (newBody, newRes) = (body.map(x => transform(x)), transform(res))
            treeCopy.Block(tree, newBody, newRes)
              .updateAttachment(TypeVariant(variantType(newRes)))

          case q"new ${ _ }[..${ tparams }](..${ params })" if tree.attachments.get[Self].isEmpty =>
            val finalRes = transform(tree.updateAttachment(Self(tree)))
            finalRes.updateAttachment(Self(finalRes))

          /*
         * Inlines access to direct constructor fields.
         * NOTE: This could also be done by the interpreter
         */
          case Select(obj @ q"new ${ _ }[..${ tparams }](..${ params })", field) if obj.symbol.asMethod.paramss.head.exists(x => x.name.toString == field.toString.trim) && field.toString.endsWith(" ") =>
            debug("Field:" + field)
            (obj.symbol.asMethod.paramss.head zip params).find(_._1.name.toString == field.toString.trim).map(_._2).get

          case Select(x, y) =>
            val nx = transform(x)
            def copy = treeCopy.Select(tree, nx, y)
            var applied = false
            val res = nx match {
              case nx if nx.symbol != null && nx.symbol.hasPackageFlag =>
                copy.updateAttachment(TypeVariant(promoteType(tree.tpe, byMode(static))))

              case Variant(_, `ct`) if tree.symbol != null && tree.symbol.isMethod && tree.symbol.asMethod.paramss.isEmpty => // interpret
                val nonPolymorphicSymbol = localTyper.typed(Select(nx, y)).symbol
                applied = true
                application(nonPolymorphicSymbol, localTyper.typed(copy), nx, Nil)

              case Variant(_, variant) =>
                copy.updateAttachment(TypeVariant(promoteType(tree.tpe, variant)))
            }
            debug(s"Select(x:${variantType(nx)}, $y): ${variant(res)}", SelectContext)

            if (tree.symbol != null && tree.symbol.isModule) res.updateAttachment(Self(tree))
            else if (applied) res.updateAttachment(Self(res))
            else nx.attachments.get[Self].foreach(self => res.updateAttachment(self))

            res

          case TypeApply(x, targs) =>
            val lhs = transform(x)
            val res = treeCopy.TypeApply(tree, lhs, targs.map(transform(_)))
            lhs match {
              case Variant(_, variant) =>
                res.updateAttachment(TypeVariant(promoteType(tree.tpe, variant)))
            }
            lhs.attachments.get[Self].foreach(self => res.updateAttachment(self))
            x.symbol
            res.attachments
            res

          case Ident(x) if tree.symbol.isModule =>
            tree.updateAttachment(TypeVariant(promoteType(tree.tpe, byMode(static))))
            tree.updateAttachment(Self(tree))

          case Ident(x) if promotedTypes.contains(tree.symbol) =>
            val res = (if (isInline(promotedTypes(tree.symbol)._1)) {
              promotedTypes(tree.symbol)._1
            } else super.transform(tree))
            debug(s"$x = $res: ${promotedTypes(tree.symbol)._2}", Idents)
            res.updateAttachment(TypeVariant(promotedTypes(tree.symbol)._2))
            res.updateAttachment(Self(promotedTypes(tree.symbol)._1))
            res

          case DefDef(_, _, _, vparams, _, _) =>
            val paramssTypes = vparams.map(p => p.map { case ValDef(_, _, tpe, _) => tpe })
            // for now treating only non-curried functions
            val skipFunction = paramssTypes.exists(_.exists(_.tpe.exists {
              case Variant(_, v @ (`ct` | `ctstatic`)) => true
              case _                                   => false
            }))
            if (skipFunction) tree else super.transform(tree)

          /*
         * Prints trees of the argument - used for debugging partial evaluation.
         */
          case Apply(x, args) if ctPackageObject(x) && x.symbol.name.toString == "showCode" =>
            val res = transform(args.head)
            localTyper.typed(q"new String(${showCode(res)})")

          /*
         * CT intrinsic promotes the types of a shared object such that:
         *   - all parameters are promoted to inline
         */
          case Apply(x, args) if ctPackageObject(x) && x.symbol.name.toString == "ct" =>
            val trArg = transform(args.head)
            if (!(variant(trArg) <:< static)) warning(s"ct can only contain static values: ${variant(trArg)} found.")
            val evalee = trArg.updateAttachment(TypeVariant(promoteType(tree.tpe, ct)))
            val res = eval(evalee).updateAttachment(TypeVariant(promoteType(tree.tpe, ct)))
            assert(variant(res) =:= ct)
            res

          case Apply(x, args) if ctPackageObject(x) && x.symbol.name.toString == "debug" =>
            debugging = true
            val res = transform(args.head)
            debugging = false
            res

          case Apply(x, args) if x.symbol != null =>
            val (lhs, transArgs) = (transform(x), args.map(transform(_)))
            application(x.symbol, tree, lhs, transArgs)

          /*
        * For valdefs that (in expressions position) we update the type
        * according to the rhs' inlinity. The rhs is stored to `promotedTypes`
        * for fetching by following Idents.
        */
          case ValDef(a, b, c, d) =>
            val rhs = transform(d)
            val newTpe = rhs.attachments.get[TypeVariant].map(_.tpe)
            newTpe.foreach(tpe => promotedTypes += (tree.symbol -> ((rhs, tpe))))
            debug(s"valdef rhs = $rhs: $newTpe", ValDefs)

            val newTypeTree = newTpe.map(TypeTree(_)).getOrElse(c)
            localTyper.typed(copyValDef(tree)(a, b, newTypeTree, rhs))

          /*
         * Type checking: if not inline, the result type is a lub of all branches and the condition.
         * Transformation: First transform the condition, if inline remove the if, and then
         * transform the branches. This prevents infinite recursion.
         */
          case If(c, t, e) =>
            val nc = transform(c)
            debug(s"if c = $nc: ${variantType(nc)}", IfStatement)
            if (isInline(nc))
              if (value[Boolean](nc)) transform(t)
              else transform(e)
            else {
              val (thn, els) = (transform(t), transform(e))
              val result = treeCopy.If(tree, nc, thn, els)
              val condType = promoteType(lub(thn.tpe :: els.tpe :: Nil), variant(nc))
              val resType = lub(condType :: variant(thn) :: variant(els) :: Nil)
              result.updateAttachment(TypeVariant(resType))
              result
            }

          case _ =>
            super.transform(tree)
        }
      }
    }
  }
}
