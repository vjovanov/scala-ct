package ch.epfl

import org.scalatest.{ FlatSpec, ShouldMatchers }
import ch.epfl.inline._

class InlineSpec extends FlatSpec with ShouldMatchers {

  "Inline" should "work with only vals" in {

    @sinline val x = List(1, 2, 3)
    x should be(List(1, 2, 3))
  }

  it should "inline the if construct if the arguments are static" in {
    @sinline val x = 1
    @sinline val y = 2
    treeString(sinline(if (x > y) "Yey!" else "Nope!")) should be("""Typed(Literal(Constant("Nope!")), TypeTree())""")
  }

  it should "work with function arguments as well" in {

    def pow(base: Long, @sinline exp: Long): Long = {
      sinline(if (exp == 0L) 1
      else base * pow(base, exp - 1))
    }

    pow(2, 0) should be(1)
    pow(2, 1) should be(2)
    pow(2, 10) should be(1024)
  }

}
