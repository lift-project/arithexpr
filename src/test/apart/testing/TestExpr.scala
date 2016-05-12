package apart.testing

import apart.arithmetic._
import org.junit.Assert._
import org.junit.{Ignore, Test}

import scala.util.Random

class TestExpr {

  private val rnd = new Random(2)

  private def rndPositive() : Int = {
    val r = rnd.nextInt(5)
    if (r == 0)
      r+1
    else if (r < 0)
      -r
    else
      r
  }

  private def rndExpr(maxDepth: Int, depth: Int=0) : ArithExpr = {

    if (depth > maxDepth)
      return Cst(rndPositive())

    rnd.nextInt(3) match {
      case 0 => rndExpr(maxDepth, depth+1) * rndExpr(maxDepth, depth+1)
      case 1 => rndExpr(maxDepth, depth+1) + rndExpr(maxDepth, depth+1)
      case 2 => rndExpr(maxDepth, depth+1) /^ rndExpr(maxDepth, depth+1)
    }
  }

  @Test def testRandom() {

    for (a <- 1 to 10) {
      val re = rndExpr(3)
      print(re)

      val oriEval = re.evalDbl
      val sim = re

      val simEval = sim.evalDbl
      assertTrue(oriEval+" != "+simEval, math.abs(oriEval-simEval) <= 1.0/1000000.0)
    }
  }

  @Test def testSimplification() {

    val c0 = Cst(0)
    val c1 = Cst(1)
    val c2 = Cst(2)
    val c10 = Cst(10)
    val result = (c0+c1)*(c10+c2)+(c10/^c2)

    assertEquals(Cst(17),result)
  }

  @Test def simplificationDiv(): Unit = {
    val N = SizeVar("N")
    val v = Var("v", RangeAdd(0,N,1))
    val result = v/N
    assertEquals(result, Cst(0))
  }

  @Test def Division(): Unit = {
    val i = Var("i")
    val M = SizeVar("M")
    assertEquals(i + i % M, i /^ M * M + i % M)
  }

  @Test def Fraction(): Unit = {
    val i = Var("i")
    val M = SizeVar("M")
    assertEquals((i / M) * M, (i / M) * M)
  }

  @Test def remainderAndModulo(): Unit = {
    val a = Var("x")
    val d = Var("d")
    assertEquals(a, (a / d) * d + a % d)
  }

  @Test def modOfVarWithVarRange(): Unit = {
    val M = SizeVar("M")
    val i = Var(GoesToRange(M))
    assertEquals(i, i % M)
  }

  @Test def modOfVarWithConstantRange(): Unit = {
    val c =  Cst(10)
    val i = Var(GoesToRange(c))
    assertEquals(i, i % c)
  }

  @Test def DivModOfVarWithConstantRange(): Unit = {
    val c =  Cst(10)
    val i = Var(GoesToRange(c))

    assertEquals(Cst(0), (i % c) / Cst(20))
  }

  @Test def modOfVarWithConstantRange2(): Unit = {
    val i = Var(GoesToRange(Cst(10)))
    assertEquals(i, i % Cst(128))
  }

  @Test def modSameDividendDivisor(): Unit = {
    val N = SizeVar("N")
    assertEquals(Cst(0), N % N)
  }

  @Test def modDivisorZero(): Unit = {
    val N = SizeVar("N")
    assertEquals(Cst(0), 0 % N)
  }

  @Test def modConstants(): Unit = {
    assertEquals(Cst(1), Cst(11) % Cst(2))
  }

  @Test def prodMultipleOfVar(): Unit = {
    val N = SizeVar("N")
    val M = SizeVar("M")
    assertTrue(ArithExpr.multipleOf(N*M, N))
  }

  @Test def prodMultipleOfProd(): Unit = {
    val N = SizeVar("N")
    val M = SizeVar("M")
    val K = SizeVar("K")
    assertTrue(ArithExpr.multipleOf(N*M*K, N*K))
  }

  @Test def divConstants(): Unit = {
    assertEquals(Cst(2), Cst(4) / Cst(2))
  }

  @Test def divPrecedence(): Unit = {
    assertEquals(Cst(0), Cst(1) / Cst(5) * Cst(5))
    assertEquals(Cst(1), Cst(1) /^ Cst(5) * Cst(5))
  }

  @Test def prodDivConstant(): Unit = {
    val N = SizeVar("N")
    assertEquals(Cst(2) * N, Cst(4) * N / Cst(2))
  }

  @Test def prodDivProdWithConstants(): Unit = {
    val N = SizeVar("N")
    val M = SizeVar("M")
    assertEquals(Cst(2) * N / M, Cst(4) * N / (Cst(2) * M))
  }

  @Test def prodDivProdWithConstants2(): Unit = {
    val N = SizeVar("N")
    val M = SizeVar("M")
    assertEquals(N / (M * Cst(2)), Cst(2) * N / (Cst(4) * M))
  }

  @Test def prodDivProdWithConstants3(): Unit = {
    val N = SizeVar("N")
    val M = SizeVar("M")
    assertEquals((N * Cst(2)) / (M * Cst(3)), Cst(2) * N / (Cst(3) * M))
  }

  @Test def prodNotMultipleOfProd(): Unit = {
    val N = SizeVar("N")
    val M = SizeVar("M")
    val K = SizeVar("K")
    assertFalse(ArithExpr.multipleOf(N*M, N*K))
  }

  @Test def cstMultipleOfCst(): Unit = {
    assertTrue(ArithExpr.multipleOf(Cst(8), Cst(4)))
  }

  @Test def prodMultipleOfCst(): Unit = {
    assertTrue(ArithExpr.multipleOf(Cst(8)*Var("i"), Cst(4)))
  }

  @Test def varWithConstantRangeDivConstant(): Unit = {
    val i = Var(RangeAdd(Cst(0), Cst(4), Cst(1)))
    assertEquals(Cst(0), i / Cst(4))
  }


  @Test def sumVarsDivConstant(): Unit = {
    val i = Var(GoesToRange(Cst(4)))
    val j = Var(GoesToRange(Var("M")))
    assertEquals(Cst(4) * j, (i + Cst(16) * j ) / Cst(4))
  }

  @Test def modNotSimplifying(): Unit = {
    val v_M_1 = Var("v_M_1")
    val v_K_2 = Var("v_K_2")
    val v_wg_id_39 = Var("v_wg_id_39", GoesToRange(v_M_1 /^ 16))
    val v_l_id_30 = Var("v_l_id_30", GoesToRange(8))
    val v_l_id_29 = Var("v_l_id_29", GoesToRange(16))
    val v_i_27 = Var("v_i_27", GoesToRange(1))
    val v_i_35 = Var("v_i_35", GoesToRange(v_K_2 /^ 8))

    val expr = ((((((((v_wg_id_39 * 16) + (((((v_l_id_30 * 16) + (v_l_id_29 * 1) + v_i_27) / 16)
      + ((((v_l_id_30 * 16) + (v_l_id_29 * 1) + v_i_27) % 16) * 8)) / 8)) * 8)
      + (((((v_l_id_30 * 16) + (v_l_id_29 * 1) + v_i_27) / 16) + ((((v_l_id_30 * 16)
      + (v_l_id_29 * 1) + v_i_27) % 16) * 8)) % 8)) / 8) + ((((((v_wg_id_39 * 16)
      + (((((v_l_id_30 * 16) + (v_l_id_29 * 1) + v_i_27) / 16) + ((((v_l_id_30 * 16)
      + (v_l_id_29 * 1) + v_i_27) % 16) * 8)) / 8)) * 8) + (((((v_l_id_30 * 16)
      + (v_l_id_29 * 1) + v_i_27) / 16) + ((((v_l_id_30 * 16) + (v_l_id_29 * 1)
      + v_i_27) % 16) * 8)) % 8)) % 8) * v_M_1)) % v_M_1) * 1) + 0 + (((v_i_35 * 8)
      + (((((((v_wg_id_39 * 16) + (((((v_l_id_30 * 16) + (v_l_id_29 * 1) + v_i_27) / 16)
      + ((((v_l_id_30 * 16) + (v_l_id_29 * 1) + v_i_27) % 16) * 8)) / 8)) * 8)
      + (((((v_l_id_30 * 16) + (v_l_id_29 * 1) + v_i_27) / 16) + ((((v_l_id_30 * 16)
      + (v_l_id_29 * 1) + v_i_27) % 16) * 8)) % 8)) / 8) + ((((((v_wg_id_39 * 16)
      + (((((v_l_id_30 * 16) + (v_l_id_29 * 1) + v_i_27) / 16) + ((((v_l_id_30 * 16)
      + (v_l_id_29 * 1) + v_i_27) % 16) * 8)) / 8)) * 8) + (((((v_l_id_30 * 16)
      + (v_l_id_29 * 1) + v_i_27) / 16) + ((((v_l_id_30 * 16) + (v_l_id_29 * 1)
      + v_i_27) % 16) * 8)) % 8)) % 8) * v_M_1)) / v_M_1)) * 1 * v_M_1)

    assertEquals(16 * v_wg_id_39 + v_l_id_29 + v_l_id_30 * v_M_1 + 8 * v_i_35 * v_M_1 + v_i_27, expr)
  }

  @Test def modSum(): Unit = {
    val N = SizeVar("N")
    assertEquals(1 % N, (N + 1) % N)
  }

  @Test def modProd(): Unit = {
    val N = SizeVar("N")
    val M = SizeVar("M")
    assertEquals(Cst(0), (N * M) % N)
  }

  @Test def OneByOne() {
    assertEquals(Cst(1), Cst(1) /^ Cst(1))
  }

  @Test def NByN() {
    val N = SizeVar("N")
    assertEquals(Cst(1), N /^ N)
  }

  @Test def zeroTimesVar(): Unit = {
    val N = SizeVar("N")
    assertEquals(Cst(0), Cst(0) * N)
  }

  @Test def zeroTimesTwo(): Unit = {
    assertEquals(Cst(0), Cst(0) * Cst(2))
  }

  @Test def simplifySumTwoMinusTwo(): Unit ={
    assertEquals(Cst(0), Cst(2) - Cst(2))
  }

  @Test def simplifySumNMinusN(): Unit ={
    val N = SizeVar("N")
    assertEquals(Cst(0), N - N)
  }

  @Test def simplifySumZeroProducts(): Unit ={
    val N = SizeVar("N")
    assertEquals(Cst(0), 4*N - 4*N)
  }

  @Test def simplifySumTwoPlusFive(): Unit ={
    assertEquals(Cst(7), Cst(2) + Cst(5))
  }

  @Test def prodEqualsConstants(): Unit = {
    assertEquals(Cst(2) * Cst(1), Cst(2) * Cst(1))
    assertEquals(Cst(1) * Cst(2), Cst(2) * Cst(1))
  }

  @Test def prodEqualsVars(): Unit = {
    val N = SizeVar("N")
    assertEquals(Cst(2) * N, Cst(2) * N)
    assertEquals(N * Cst(2), Cst(2) * N)
  }

  @Test def sumEqualsConstants(): Unit = {
    assertEquals(Cst(2) + Cst(1), Cst(2) + Cst(1))
    assertEquals(Cst(1) + Cst(2), Cst(2) + Cst(1))
  }

  @Test def sumEqualsVars(): Unit = {
    val N = SizeVar("N")
    assertEquals(Cst(2) + N, Cst(2) + N)
    assertEquals(N + Cst(2), Cst(2) + N)
  }

  @Test def powSimplify(): Unit = {
    val N = SizeVar("N")
    val expr = Pow( 1*1*Pow(2, -1), Log(2, N) + (1  * -1) ) * N
    assertEquals(Cst(2), expr)
  }

  @Test def minusOneTimesMinusFive(): Unit = {
    assertEquals(Cst(5), Cst(-1) * Cst(-5))
  }

  @Test def modBug(): Unit = {
    val n = SizeVar("N")
    val l = Var("l", ContinuousRange(0, 4))
    val wg = Var("wg", ContinuousRange(0, n/^4))

    assertEquals(Cst(0), (l * n/^4) % (n/^4))
    assertEquals(wg, wg % (n/^4))
    assertEquals(wg, (wg + l * n/^4) % (n/^4))
    assertEquals(wg, wg % n)
    assertEquals(l * n/^4, (l * n/^4) % n)
  }

  // Test that the % operator is the same as C (ISO14882:2011(e) 5.6-4)
  @Test def NegativeMod(): Unit = {
    // -11 % 5 = -1
    assertEquals(Cst(-1), Cst(-11) % Cst(5))
    // 11 % -5 = 1
    assertEquals(Cst(1), Cst(11) % Cst(-5))
  }

  @Test
  def divPlusModMultiplied(): Unit = {
    val a = Var("a")
    val d = Var("d")
    val x = Var("x")

    assertEquals(x*a, x * (a / d) * d + x * (a % d))
  }

  @Test
  def divPlusModMultipliedConstants(): Unit = {
    val a = Var("a")
    val d = Cst(2)
    val x = Cst(8)

    assertEquals(x*a, x * (a / d) * d + x * (a % d))
  }

  @Test
  def evalAtMaxWithSumAndConstants(): Unit = {
    val i = Var("i", ContinuousRange(0, 2))
    val id = Var("id", ContinuousRange(0, 4))

    // 0 <= id + 4*i <= 7 < 8
    assertEquals(Cst(0), (id + 4*i) / 8)
    assertEquals(id + 4*i, (id + 4*i) % 8)
  }

  @Test
  def divByOpposite(): Unit = {
    val a = Var("a")

    assertEquals(Cst(-1), Cst(-4)/Cst(4))
    assertEquals(Cst(-1), (-4*a)/(4*a))
    assertEquals(Cst(-1), (-4*a)/^(4*a))
  }

  @Test
  def diffProdVal(): Unit = {
    val a = Var("a")
    assertEquals(a, a + a - a)
    assertEquals(Cst(2), (2 + a) + (a * -1))
  }

  @Test
  def divPlusModOfSumMultipliedConstants(): Unit = {
    val a = Var("a")
    val b = Var("b")
    val d = Cst(2)
    val x = Cst(8)

    assertEquals(a, (a / d) * d + (a % d))
    assertEquals(a+b, ((a+b) / d) * d + ((a+b) % d))
    assertEquals(a*b, ((a*b) / d) * d + ((a*b) % d))
    assertEquals(x*a, x * (a / d) * d + x * (a % d))
    assertEquals(x*(a+b), x * ((a + b) / d) * d + x * ((a + b) % d))
  }

  @Test
  def sumFraction(): Unit = {
    val n = SizeVar("N")
    val i = Var("i", ContinuousRange(0, n))

    // N <= i + N <= 2*N - 1 < 2*N
    assertEquals(Cst(1), (i+n) / n)
  }

  @Test
  def minFunction(): Unit = {
    import ArithExpr.Math._

    // comparing 0 and 1
    assertEquals(Cst(0), Min(Cst(0),Cst(1)))
    // negative number
    assertEquals(Cst(-1), Min(Cst(-1),Cst(1)))
    assertEquals(Cst(-2), Min(Cst(-1),Cst(-2)))

    val n = SizeVar("N")
    // unknown var1
    assertEquals(Min(n, Cst(0)), Min(n, Cst(0)))
    // unknown var2
    assertEquals(Min(Cst(0),n), Min(Cst(0),n))
    // equal values
    assertEquals(n*10, Min(n*10,n*10))

    // unknown plus offset
    assertEquals(n+5, Min(n+5,n+10))
    // this should not simplify
    assertEquals(Min(n,n*2), Min(n,n*2))
  }

  @Test
  def maxFunction(): Unit = {
    import ArithExpr.Math._

    // comparing 0 and 1
    assertEquals(Cst(1), Max(Cst(0),Cst(1)))
    // negative number
    assertEquals(Cst(1), Max(Cst(-1),Cst(1)))
    assertEquals(Cst(-1), Max(Cst(-1),Cst(-2)))

    val n = SizeVar("N")
    // unknown var1
    assertEquals(Max(n, Cst(0)), Max(n, Cst(0)))
    // unknown var2
    assertEquals(Max(Cst(0),n), Max(Cst(0),n))
    // equal values
    assertEquals(n*10, Max(n*10,n*10))

    // unknown plus offset
    assertEquals(n+10, Max(n+5,n+10))
    // this should not simplify*/
    assertEquals(Max(n,n*2), Max(n,n*2))
  }

  @Test
  def testIfThenElse(): Unit = {
    val a = Var("a")
    val b = Var("b")
    val c = Var("c")

    // True condition
    assertEquals(a, (Cst(1) lt Cst(2)) ?? a !! b)
    // False condition
    assertEquals(b, (Cst(1) gt Cst(2)) ?? a !! b)
    // Identical branches
    assertEquals(a, (b ne c) ?? a !! a)
    // Unevaluable predicate with positive offset on the LHS
    assertEquals(c, (b+Cst(2) gt b) ?? c !! b)
    // Unevaluable predicate with positive offset on the RHS
    assertEquals(b, (b+Cst(-2) gt b ) ?? c !! b)
  }

  @Test
  def bugAIsSmaller(): Unit = {
    val i = Var("i", ContinuousRange(0, 2))
    val id = Var("id", ContinuousRange(0, 5))

    // 0 <= id + 4*i <= 8 < 9
    assertNotEquals(Cst(0), (id + 4*i) / 8)
    assertNotEquals(id + 4*i, (id + 4*i) % 8)
  }

  @Test
  def bugBIsSmaller(): Unit = {
    val n = SizeVar("N")
    val l = Var("l", ContinuousRange(0, 4))

    assertTrue(ArithExpr.isSmaller(l * n/^4, n))
  }

  @Test
  def fractionMultipleOf(): Unit = {
    val n = SizeVar("N")

    assertTrue(ArithExpr.multipleOf(n / 4, n / 8))
    assertTrue(ArithExpr.multipleOf(3 * n / 4, n / 8))
  }

  @Test
  def varFractionProductMultipleOf(): Unit = {
    val n = SizeVar("N")
    val i = Var("i")

    assertTrue(ArithExpr.multipleOf(i* n / 4, n / 8))
  }

  @Test
  def equalMultipleOf(): Unit = {
    val n = SizeVar("N")
    assertTrue(ArithExpr.multipleOf(n, n))
  }

  @Test
  def divisionMultipleOf(): Unit = {
    val n = SizeVar("N")

    assertTrue(ArithExpr.multipleOf(n /^ 4, n /^ 8))
    assertTrue(ArithExpr.multipleOf(3 * n /^ 4, n /^ 8))
    assertFalse(ArithExpr.multipleOf(n /^ 8, n /^ 4))
    assertFalse(ArithExpr.multipleOf(n /^ 8, n))
  }

  @Ignore
  @Test
  def divisionSmallerThan(): Unit = {
    val l = Var("l", GoesToRange(64))

    assertTrue(ArithExpr.isSmaller(l / 16, 8))
  }

  @Test
  def modOfDivisionMultiple(): Unit = {
    val n = SizeVar("N")

    assertEquals(Cst(0), (n /^ 4) % (n /^ 8))
//    assertEquals(n / 8, (n / 8) % (n / 4))
  }

  @Test
  def subtractProds(): Unit = {
    val expr1: ArithExpr = SizeVar("N") * 1 /^ 4
    val expr2: ArithExpr = expr1 + 1

    assertEquals(Cst(1), expr2 - expr1)
  }

  @Test def Equality(): Unit = {
    val a = Var("a"); val b = Var("a")
    val expr1 = Cst(2)*(a+b)
    val expr2 = Cst(2)*a + Cst(2)*b
    assertEquals(expr1, expr2)
  }
}
