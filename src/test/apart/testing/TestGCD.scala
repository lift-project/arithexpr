package apart.testing

import apart.arithmetic._
import org.junit.Assert._
import org.junit.Test

/**
 * Test class for Greatest Common Divisor operator
 */
class TestGCD {
  val a = Var("a")
  val b = Var("b")
  val c = Var("c")


  @Test
  def TestCst(): Unit = {
    assertEquals(Cst(5), ArithExpr.gcd(Cst(10), Cst(5)))
    assertEquals(Cst(25), ArithExpr.gcd(Cst(100), Cst(25)))
    assertEquals(Cst(11), ArithExpr.gcd(Cst(33), Cst(11)))
  }

  @Test
  def TestPows(): Unit = {
    assertEquals(a, ArithExpr.gcd(a, a pow 2))
    assertEquals(a*a, ArithExpr.gcd(a*a, a pow 2))
    assertEquals(a pow 2, ArithExpr.gcd(a pow 3, a pow 2))
  }

  @Test
  def TestVars(): Unit = {
    assertEquals(2*a*b, ArithExpr.gcd(4*a*b, 6*a*b*c))
    assertEquals(Cst(2), ArithExpr.gcd(4*a, 2))
    assertEquals(a*b, ArithExpr.gcd(a*b*a*b, a*b*c))

    // todo fix: causes hash collision for Prods ac and bc non-deterministically
    //assertEquals(a+b,     ArithExpr.gcd(a*a + a*b, a*c + b*c))
    assertEquals(a,       ArithExpr.gcd(a + a*b + a*c, a))

    assertEquals(Cst(1),  ArithExpr.gcd(a + a*b + a*c, a + b))

    assertEquals(a,       ArithExpr.gcd(-1*a, a))

    assertEquals(a,       ArithExpr.gcd(2*a,-1*a))


    assertEquals(Cst(1), ArithExpr.gcd(Cst(2)*a + Pow(a,Cst(2)), Cst(2) + a))
  }
}
