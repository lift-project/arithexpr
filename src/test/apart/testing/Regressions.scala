package apart.testing

import apart.arithmetic.{ArithExpr, Var, Cst}
import org.junit.Assert._
import org.junit.Test

/**
 * Contains the generated expression failing the C cross validation
 */
class Regressions {
  val a = Var("a")
  val b = Var("b")
  val c = Var("c")
  val d = Var("d")
  val valmap = Map[ArithExpr, ArithExpr](
    (a, Cst(12)),
    (b, Cst(57)),
    (c, Cst(2)),
    (d, Cst(4))
  )

  @Test def expr1(): Unit = {
    val expr = (a * -1) / c
    assertEquals(Cst(-6), ArithExpr.substitute(expr, valmap))
  }

  @Test def expr2(): Unit = {
    val expr = ((1+(-1*b)) % c)-1
    assertEquals(Cst(-1), ArithExpr.substitute(expr, valmap))
  }

  @Test def expr3(): Unit = {
    val expr = (9*((2+15)) / (13))-108
    assertEquals(Cst(-97), ArithExpr.substitute(expr, valmap))
  }

  @Test def expr4(): Unit = {
    val lhs = Cst(25958400) * Cst(1) / ((Cst(18) * a) + (Cst(12480) * (a pow Cst(2)))) * (a pow Cst(3))
    val rhs = Cst(37440) * Cst(1) / ((Cst(18) * a) + (Cst(12480) * (a pow Cst(2)))) * (a pow Cst(2))
    System.out.println(lhs)
    System.out.println(rhs)
    System.out.println(lhs + rhs)
  }

  @Test def expr5(): Unit = {
    val expr = (a pow 2) + (3*1/(32)*1/(5)*1/(13)*a)
  }

  @Test def expr6(): Unit = {
    val lhs = (Cst(3) * Cst(1) / (Cst(4)) * Cst(1) / (a) * Cst(1) / (Cst(5)) * Cst(1) / (Cst(7))) + (Cst(104) * Cst(1) / (c) * c * 1 / (Cst(7)))
    val rhs = Cst(1747200) * a * Cst(1) / (((Cst(18) * c) + (Cst(12480) * (c pow 2)))) * (c pow Cst(2))
    lhs * rhs
  }

  @Test def expr7(): Unit = {
    val expr = (3*a*b)
    assertEquals(a*b*11, a*b*6 + a*b*5)
    assertNotEquals(a*b*11, a*b*6 + a*5)
  }

}
