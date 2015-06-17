package ch.epfl

import scala.annotation.StaticAnnotation

/*
 *  BT Parameters and type checking:
 *  class Vector<cVector, cT, cT <: cVector>[T](val store: Array<cVector, cT>[T])
 *    extends Iterable<cVector, cT>[T] {
 *
 *    (def length: Int|<CVector>|)<cVector> = store.length
 *
 *    (def hashCode: Int|<CVector v cT>|)<cVector> = {
 *      // TODO should we infer here or put a bottom or put a top???
 *      (<cx, cVector <: cx> def hash(x: Any<chash>): Int|<cx>| = x.hashCode)<cVector>
 *      store.foldLeft<cVector, cVector v ct>(0<cVector>)(hash)<cVector>)
 *
 *    (def map<cMap, cU, cU <: cMap>[U](f: (T<cT> => U<cU>)<cMap>): Vector<cVector, cU>[U])<cVector> = {
 *      val newArray = new Array<cVector v cMap, cU>[U](store.size)
 *      var i: Int|<cVector v cMap>| = 0<cVector v cMap>
 *      val x: Any|<cT>| = store.head // TODO insert this example somewhere!!!
 *      store.foreach<cVector v cMap>({ (x: T<cT>) =>
 *        newArray(i) = f(store(i))
 *        i += 1<cVector v cMap>
 *      }<cVector v cMap>)
 *      new Vector<cVector v cMap, cU>[U](newArray)
 *    }
 *
 *    def foo<cFoo>(x: T, f: <cf, cf1, cf2, cf <: cFoo>(Any => Int)): Int|<cT, cT <: cf1 >| = f(x)
 *
 *  }
 *
 * BT inference:
 *
 *
 *
 */

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
