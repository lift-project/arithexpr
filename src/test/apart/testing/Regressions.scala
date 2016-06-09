package apart.testing

import apart.arithmetic._
import apart.arithmetic.SizeVar
import org.junit.Assert._
import org.junit.Test

/**
 * Contains the generated expression failing the C cross validation
 */
//noinspection ScalaUnnecessaryParentheses
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
    val expr = (9* (2 + 15) / 13)-108
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
    (a pow 2) + (3*1/ 32 *1/ 5 *1/ 13 *a)
  }

  @Test def expr6(): Unit = {
    val lhs = (Cst(3) * Cst(1) / Cst(4) * Cst(1) / a * Cst(1) / (Cst(5)) * Cst(1) / (Cst(7))) + (Cst(104) * Cst(1) / (c) * c * 1 / (Cst(7)))
    val rhs = Cst(1747200) * a * Cst(1) / (((Cst(18) * c) + (Cst(12480) * (c pow 2)))) * (c pow Cst(2))
    lhs * rhs
  }

  @Test def expr7(): Unit = {
    (3*a*b)
    assertEquals(a*b*11, a*b*6 + a*b*5)
    assertNotEquals(a*b*11, a*b*6 + a*5)
  }

  @Test def expr8(): Unit = {
    assertEquals(a /^ 2048, a * 128 * 1 /^ (262144))
  }

  @Test def expr9(): Unit = {
    val a = Var("a")
    assertEquals(a /^ 2, a * (a*1/^(2)) /^ a)
  }

  class func1(a: Int) extends ArithExprFunction("func1") {
    override lazy val digest: Int =  0x3105f133 ^ range.digest() ^ name.hashCode ^ a.hashCode()

    override lazy val toString: String = s"$name($a)"

    override lazy val sign: Sign.Value = Sign.Positive

    override lazy val (min : ArithExpr, max: ArithExpr) = (Cst(0),PosInf)

    override def substituteDiv = this
  }

  class func2(a: Int) extends ArithExprFunction("func2") {
    override lazy val digest: Int =  0x3105f133 ^ range.digest() ^ name.hashCode ^ a.hashCode()

    override lazy val toString: String = s"$name($a)"

    override lazy val sign: Sign.Value = Sign.Positive

    override lazy val (min : ArithExpr, max: ArithExpr) = (Cst(0),PosInf)

    override def substituteDiv = this
  }

  @Test def expr10(): Unit = {
    assertNotEquals(Cst(0), new func1(0) - new func2(0))
    assertNotEquals(Cst(10), new func1(6) + new func1(4))
    assertNotEquals(Cst(10), new func1(6) + new func1(4))
    assertNotEquals(new func1(10), new func1(6) + new func1(4))
  }

  @Test def expr11(): Unit = {
    val v_l_id_8 = Var("a")
    val v_l_id_7 = Var("b")

    assertNotEquals(v_l_id_7 % 8, (((v_l_id_8 * 4) + v_l_id_7) % 8) * 1)
    assertEquals((v_l_id_8 * 4) + v_l_id_7, 0 + ((((v_l_id_8 * 4) + v_l_id_7) / 8) * 8 * 1) + ((((v_l_id_8 * 4) + v_l_id_7) % 8) * 1))
  }

  @Test
  def divPlusModOfSumMultipliedConstants(): Unit = {
    val a = Var("a")
    val b = Var("b")
    val x = Cst(8)

    assertEquals(x * Cst(4) * (a+b), x * (Cst(4) * (a + b) / Cst(16)) * Cst(16) + x * (Cst(4) * (a + b) % Cst(16)))
  }

  @Test
  def expr12(): Unit = {
    val v_N_0 = SizeVar("v_N_0")
    val v_wg_id_249 = PosVar("v_wg_id_249")
    val v_wg_id_246 = Var("v_wg_id_246", ContinuousRange(0, v_N_0 / 64))
    assertEquals(64 * v_N_0 * v_wg_id_249 + 7 * v_N_0 + v_N_0 * new func1(1) * 8 + 48 + new func1(0) + 64 * v_wg_id_246,
      (64 * v_N_0 * v_wg_id_249) + (7 * v_N_0) + (v_N_0 * new func1(1) * 8) + (
        ((v_wg_id_246 + (v_N_0 * new func1(1) / 8) + (7 * v_N_0 / 64)) % (v_N_0 / 64))
          * 64) + 48 + new func1(0))
  }

  @Test
  def expr13(): Unit = {
    assertNotEquals(? / ?, 1)
  }
    class OclFunction(name: String, range: Range)
      extends ArithExprFunction(name, range) {

      override lazy val (min : ArithExpr, max: ArithExpr) = (range.min.min, range.max.max)
      override lazy val sign: Sign.Value = Sign.Positive

      override def substituteDiv = this
    }
  @Test
  def expr14(): Unit = {

    val N = Var("N", StartFromRange(Cst(1)))
    val get_group_id = new OclFunction("get_group_id", ContinuousRange(0, 2))
    val get_num_groups = new OclFunction("get_num_groups", ContinuousRange(1, PosInf))
    val wg_id = Var("wg_id", RangeAdd(get_group_id, N/^8, get_num_groups))
    val get_local_id = new OclFunction("get_local_id", ContinuousRange(0, 2))

    val f = (i: ArithExpr) => i / 8 + ((i % 8) * N /^ 8)
    val i = 2 + (4 * get_local_id) + (8 * wg_id)
    val output = f(i)

    val expected = N /^ 4 + (get_local_id * N /^ 2) + wg_id
    assertEquals(expected, output)
  }

  @Test
  def expr15(): Unit = {
    val get_local_id = new OclFunction("get_local_id", ContinuousRange(0, 2))
    assertTrue(ArithExpr.isSmaller( 1+(2*get_local_id), 4 ).getOrElse(false))
  }
}
