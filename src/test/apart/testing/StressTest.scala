package apart.testing

import apart.arithmetic._
import apart.arithmetic.simplifier.ExprSimplifier
import apart.tools.ExprPrinter
import org.junit.Test

/**
 * Stress test for algebraic simplification.
 * This is not a functional test, there is no cross validation.
 */
class StressTest {

  // var pool
  val pool = List(Var("a"), Var("b"), Var("c"), Var("d"))

  val rd = new scala.util.Random(1)

  /**
   * Return a random new term.
   * @return Either one or a variable or a constant.
   */
  def getTerm(): ArithExpr = {
    val c = rd.nextInt(3)
    if(c == 0) pool(rd.nextInt(pool.length))
    else Cst(rd.nextInt(20)+1)
  }

  def addTerm(a: ArithExpr): ArithExpr = {
    val seed = rd.nextInt(25)
    val other = getTerm()
    if      (seed < 10) a * other
    else if (seed < 13) a - other
    else if (seed < 16) a / (other + 1)
    else if (seed < 19) a /^ other
    else if (seed < 21) a % other
    else                a + other
  }

  @Test
  def largeExp(): Unit = {
    var a = getTerm()
    var b = a

    for( i <- 0 to 70) {
      val start = System.currentTimeMillis()
      a = addTerm(a)
      val adding = System.currentTimeMillis()
      b = ExprSimplifier(a)
      val simplifying = System.currentTimeMillis()
      println("%d, %f, %f".format(i, (adding - start)/1000.0, (simplifying - adding)/1000.0))
    }
    b = ExprSimplifier(a)
    ExprPrinter.dot(b)
  }
}
