package ch.epfl.scalact

import scala.annotation.StaticAnnotation

/**
 * Annotation used internally to introduce binding-time variables.
 * @param btvars list of variable names.
 */
final case class BTParams(btvars: List[String]) extends StaticAnnotation

/**
 * Annotation used internally to track binding-time equations.
 */
case class BT(expr: String) extends StaticAnnotation

