package library

sealed trait List[+T] {
  def head: T
  def tail: List[T]

  def zip[U](l: List[U]): List[Tuple2[T, U]] = if (this == Nil) {
    Nil
  } else {
    new Cons[Tuple2[T, U]](
      new Tuple2(
        head,
        l.head),
      tail.zip(l.tail))
  }

  def zipWithIndex: List[Tuple2[T, Int]] = zipWithStartingIndex(0)

  def zipWithStartingIndex(starting: Int): List[Tuple2[T, Int]] = if (this == Nil) {
    Nil
  } else {
    new Cons(
      new Tuple2(
        head,
        starting),
      tail.zipWithStartingIndex(starting + 1))
  }

  def map[U](f: T => U): List[U] = if (this == Nil) {
    Nil
  } else {
    new Cons(f(head), tail.map(f))
  }

  def foldLeft[U](z: U, f: (U, T) => U): U = {
    if (this == Nil)
      z
    else
      tail.foldLeft(f(z, head), f)
  }

  def length: Int = if (this == Nil) 0 else tail.length + 1
}

class Cons[T](val head: T, val tail: List[T]) extends List[T] {
  override def equals(that: Any): Boolean = {
    val thatList = that.asInstanceOf[List[Any]]
    thatList.head == head && thatList.tail == tail
  }
}

object Nil extends List[Nothing] {
  def head: Nothing = throw new RuntimeException("Head of the empty list!")
  def tail: List[Nothing] = throw new RuntimeException("Tail of the empty list!")
}

/*
 * Does not work with the interpreter!
 */
object List {
  def apply[T](x1: T, x2: T, x3: T, x4: T): List[T] =
    new Cons(x1, new Cons(x2, new Cons(x3, new Cons(x4, Nil))))
  def apply[T](x1: T, x2: T, x3: T): List[T] =
    new Cons(x1, new Cons(x2, new Cons(x3, Nil)))
  def apply[T](x1: T, x2: T): List[T] =
    new Cons(x1, new Cons(x2, Nil))
  def apply[T](x1: T): List[T] =
    new Cons(x1, Nil)
  def apply[T](): List[T] =
    Nil
}

class Tuple2[+T, +U](val _1: T, val _2: U) {
  override def equals(x: Any): Boolean = {
    if (x.isInstanceOf[Tuple2[Any, Any]]) {
      val that = x.asInstanceOf[Tuple2[Any, Any]]
      (this._1 equals that._1) && (this._2 == that._2)
    } else false
  }
  override def toString: String = s"(${_1},${_2})"
}

import ch.epfl.scalact._

/*@ctv
object Numeric {
  @ctv implicit def dnum(): Numeric[Double @ctv?] @ct = DoubleNumeric
}

trait Numeric[T] {
  @ctv def plus(x: T, y: T): T
  @ctv def minus(x: T, y: T): T
  @ctv def times(x: T, y: T): T
  @ctv def fromInt(x: Int): T

  @ctv def zero(): T
  @ctv def one(): T

  @ct
  class Ops(lhs: T) {
    @ctv def +(rhs: T) = plus(lhs, rhs)
    @ctv def -(rhs: T) = minus(lhs, rhs)
    @ctv def *(rhs: T) = times(lhs, rhs)
  }

  @ctv implicit def mkNumericOps(lhs: T): Ops = new Ops(lhs)
}

object DoubleNumeric extends Numeric[Double] {
  @ctv def plus(x: Double @ctv?, y: Double @ctv?): Double @ctv? = x + y
  @ctv def minus(x: Double @ctv?, y: Double @ctv?): Double @ctv? = x - y
  @ctv def times(x: Double @ctv?, y: Double @ctv?): Double @ctv? = x * y
  @ctv def fromInt(x: Int @ctv?): Double = x
  @ctv def one: Double = 1.0
  @ctv def zero: Double = 0.0
}

// Full blown solution
@ct object Numeric {
  @ctv implicit def dnum[T <: Double](): Numeric[T] @ctv =
    ct[T](DoubleNumeric)
}

 trait Numeric[T] {
   def plus(x: T, y: T): T
   def minus(x: T, y: T): T
   def times(x: T, y: T): T
   def fromInt(x: Int): T

   def zero(): T
   def one(): T

   class Ops(lhs: T) {
    def +(rhs: T) = plus(lhs, rhs)
    def -(rhs: T) = minus(lhs, rhs)
    def *(rhs: T) = times(lhs, rhs)
  }

  @ctv implicit def mkNumericOps(lhs: T): Ops = new (Ops@ctv)(lhs)
}

@ct? object DoubleNumeric extends Numeric[Double@ct?]@ctv {
  @ctv def plus(x: Double @ct?, y: Double @ct?): Double@ct? = x + y
  @ctv def minus(x: Double @ct?, y: Double @ct?): Double@ct? = x - y
  @ctv def times(x: Double @ct?, y: Double @ct?): Double@ct? = x * y
  @ctv def fromInt(x: Int @ct?): Double @ct? = x
  @ctv def one: Double@ct? = ct?(1.0)
  @ctv def zero: Double@ct? = ct?(0.0)
}*/

// What happens to narrowed polymorphic types? @ct? should solve this.
// Soundness of the whole approach? Read the papers?
// Implementation: work on it until 1st June.
