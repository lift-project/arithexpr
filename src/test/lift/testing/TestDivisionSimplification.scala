package lift.testing

import lift.arithmetic.{Cst, Var}
import org.junit.Test
import org.junit.Assert.assertEquals

class TestDivisionSimplification {
  val a = Var("a")
  val b = Var("b")
  val c = Var("c")

  @Test
  def simpleFactorization(): Unit = {
    assertEquals(b, (Cst(42) * b + a * b) /^ (Cst(42) + a))
    assertEquals(a, (Cst(42) * a + b * a) /^ (Cst(42) + b))
  }
  
  @Test
  def factorizationInAffineExpr(): Unit = {
    assertEquals(
      c + a /^ (Cst(42) + b),
      (a + Cst(42) * c + b * c) /^ (Cst(42) + b)
    )
  }
}