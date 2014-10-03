package ch.epfl

import org.scalatest.{ FlatSpec, ShouldMatchers }
import ch.epfl.inline._

class InlineSpec extends FlatSpec with ShouldMatchers {

  "Inline" should "work with only vals" in {

    // @sinline val x = List(1, 2, 3)

    // x should be(List(1, 2, 3))
  }

  it should "inline the if construct if the arguments are static" in {
    // @sinline val x: Int = 1
    // treeString(sinline(if (x > 3) "Yey!" else "Nope!")) should be("""Typed(Literal(Constant("Nope!")), TypeTree())""")
  }

  it should "work with function arguments as well" in {

    def pow(base: Long, @sinline exp: Long): Long = {
      // TODO sinline can't go here as it fires before the outer macro does
      if (exp == 0) 1 else base * pow(base, exp - 1)
    }

    treeString(pow(2, 10)) should be("""Typed(Literal(Constant(1024)), TypeTree())""")
  }

}
