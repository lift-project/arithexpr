package lift.testing

import lift.arithmetic._
import lift.arithmetic.simplifier.SimplifyPow
import lift.arithmetic.ArithExpr._
import org.junit.Assert.assertEquals
import org.junit.Test

class TestSumAndProdSimplification {
  @Test
  def testWithRanges(): Unit = {
    val a = Var("a", RangeMul(1, 2048, mul = 2), Some(2))
    val d = Var("d", RangeAdd(2, 224, step = 2), Some(3))
    val c = Var("c", RangeAdd(1, 16, 1), Some(5))
    val b = Var("b", RangeMul(1, 2048, mul = 2), Some(6))
    val e = Var("e", RangeAdd(1, 4, 1), Some(7))
    val f = Var("f", RangeAdd(1, d, step = 1), Some(9))

    val exprB_1 = a*SimplifyPow(c*d,2)
    val exprB_2 = SimplifyPow(c*f, -1)

    val exprB = exprB_1 * exprB_2
    // Checking against StackOverflows
  }

  @Test
  def tests(): Unit = {
    SimplificationLevel.assumeLevelNoLessThan(SimplificationLevel.O1)

    val a = Var("a")
    val b = Var("b")
    val c = Var("c")
    val d = Var("d")
    val e = Var("e")

    val exprA_1 = a * c.pow(2) * d.pow(2)
    val exprA_2 = e.pow(2)
    val exprA = exprA_1 * exprA_2

    val expr0_1 = a * b * c.pow(-1)
    val expr0 = expr0_1 * d.pow(-1)

    val expr_1 = a*b + c*d
    assertEquals(expr_1, a*b + c*d)

    val expr_2 = a.pow(2) * a
    assertEquals(expr_2, a.pow(3))

    val expr_3 = 2 * a * b /^ a
    assertEquals(expr_3, 2 * b)

    val expr_4 = a + b
    assertEquals(expr_4, a + b)

    val expr_5_1 = a.pow(2) + 2*a*b + b.pow(2)
    val expr_5_2 = (a + b).pow(2)
    assertEquals(expr_5_1, expr_5_2)
    //
    val expr_6 = SimplifyPow(a, 2) + SimplifyPow(b, 2) + SimplifyPow(c, 2) + 2*a*b + 2*a*c + 2*b*c
    assertEquals(expr_6, (a + b + c).pow(2))
    //
    //    println(expr4.asInstanceOf[Sum].powOfSumRepresentation)

    val expr_7_1 = 1 /^ (a + b + c)
    val expr_7_2 = a.pow(2) + b.pow(2) + c.pow(2) + 2*a*b + 2*a*c + 2*b*c
    val expr_7 = expr_7_1 * expr_7_2
    assertEquals(expr_7, a + b + c)

    val expr_8_1 = 1/^(a + b)
    val expr_8_2 =
      d * a +
        d * b
    val expr_8 = expr_8_1 * expr_8_2
    assertEquals(expr_8, d)

    val expr_9_1 = 1/^(a + b)
    val expr_9_2 =
      1/^d * a.pow(2) +
        1/^d * b.pow(2) +
        1/^d * 2*a*b
    val expr_9 = expr_9_1 * expr_9_2
    assertEquals(expr_9, 1/^d * (a + b))

    val expr_10 =
      a * a.pow(2) +
        a * b.pow(2)
    //        (a + b) * 2*a*b
    assertEquals(expr_10, a * (a.pow(2) + b.pow(2)))

    val expr_11_1 = 2 * a * b * 1/^(a+b)
    val expr_11_2 = a * a * 1/^(a+b)
    val expr_11 = ArithExpr.gcd(expr_11_1, expr_11_2)
    //    assertEquals(expr_11, (a * 1/^(a+b)))

    val expr_12_1_1 = a * 1/^(a+b)
    val expr_12_1_2 = a.pow(2)  *  1/^(a+b)
    val expr_12_2 = expr_12_1_1 + expr_12_1_2
    val expr_12 =  a * 1/^(a+b) * (1 + a)
    assertEquals(expr_12_2, expr_12)

    val expr_13_1 = a * 1/^(a+b) + a.pow(2) * 1/^(a+b)
    val expr_13_2 = 1/^(a+b)
    val expr_13 = expr_13_1 /^ expr_13_2
    assertEquals(expr_13, a + a.pow(2))

    val expr_14_1 = 2 * a * b * 1/^(a+b) + a.pow(2) * 1/^(a+b)
    val expr_14_2 = 1/^(a+b)
    val expr_14 = expr_14_1 /^ expr_14_2
    assertEquals(expr_14, 2 * a * b + a.pow(2))

    val expr15_1 = 1/^(a + b) * a.pow(2) + 1/^(a + b) * 2*a*b
    val expr15_2 = 1/^(a + b) * b.pow(2)

    val expr15 = expr15_1 + expr15_2
    assertEquals(expr15, a + b)

    val expr_16_1 = 1/^(a + b) * c * a.pow(2) + 1/^(a+b) * c * 2*a*b
    val expr_16_2 = 1/^(a + b) * c * b.pow(2)

    val expr_16 = expr_16_1 + expr_16_2
    assertEquals(expr_16, c * (a + b))

    val expr17_1 = 1/^(a + b) * a.pow(2) + 1/^(a + b) * 2*a*b
    val expr17_2 = 1/^(a + b) * b.pow(2) + c

    val expr_17 = expr17_1 + expr17_2
    // TODO: make this pass
//    assertEquals(expr_17, (a + b) + c)

    val expr_18_1 = 1/^(a + b) * 3 * a.pow(2) + 1/^(a+b) * 3 * 2*a*b
    val expr_18_2 = 1/^(a + b) * 3 * b.pow(2)

    val expr_18 = expr_18_1 + expr_18_2
    assertEquals(expr_18, 3 * (a + b))

  }
}
