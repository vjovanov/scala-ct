package ch.epfl

import scala.annotation.StaticAnnotation

package object scalact {

  sealed trait Variant extends StaticAnnotation

  /*
   * Internal marker trait that carries the information that a type is dynamic.
   * This is added since absence of this type requires special handling in several
   * locations.
   */
  class rt extends Variant { override def toString: String = "rt" }

  /*
   * Marker trait that denotes that all operations on the type will be executed at
   * compile-time.
   */
  class ct extends static { override def toString: String = "ct" }

  /*
   * Marker trait that denotes that if the function argument will be converted to
   * inline if Internal marker trait that carries the information that a type is dynamic.
   * This is added since absence of this type requires special handling in several
   * locations.
   */
  class static extends rt // TODO eliminate

  /**
   * Partially evaluates the body (must be static) and returns an inline version of the
   * type T. All operations on the return type will be inlined and all non-generic
   * arguments @ct.
   */
  def ct[T](body: => T): T = ???

  /**
   * Prints the code of the partially evaluated body.
   *  This method is primarily used for debugging purposes.
   */
  def showCode(body: => Any): String = ???

  /**
   * Prints the code of the partially evaluated body.
   *  This method is primarily used for debugging purposes.
   */
  def debug(body: => Any): String = ???

}
