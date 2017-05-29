package lift.testing

import lift.arithmetic._
import org.junit.Assert._
import org.junit.{Ignore, Test}

import scala.util.Random

class OclTestFunction private(name: String, range: Range)
  extends ArithExprFunction(name, range) {

  lazy val toOCLString = s"$name()"
  override lazy val digest: Int = HashSeed ^ /*range.digest() ^*/ name.hashCode
  override val HashSeed = 0x31111111
  override def equals(that: Any) = that match {
    case f: OclTestFunction => this.name.equals(f.name)
    case _ => false
  }
  override lazy val (min : ArithExpr, max: ArithExpr) = (range.min.min, range.max.max)
  override lazy val sign: Sign.Value = Sign.Positive

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(new OclTestFunction(name, range.visitAndRebuild(f)))
}

object OclTestFunction {
  def apply(name: String, range: Range = RangeUnknown) : OclTestFunction =
    new OclTestFunction(name, range)
}

object get_num_groups {
  def apply(range : Range = ContinuousRange(1, PosInf)) =
    OclTestFunction("get_num_groups", range)
}

object get_global_size {
  def apply(range : Range = ContinuousRange(1, PosInf)) =
    OclTestFunction("get_global_size", range)
}

object get_local_size {
  def apply(range : Range = ContinuousRange(1, PosInf)) =
    OclTestFunction("get_local_size", range)
}

object get_local_id {
  def apply(range : Range) =
    OclTestFunction("get_local_id", range)

  def apply() =
    OclTestFunction("get_local_id", ContinuousRange(0, get_local_size()))
}

object get_global_id {
  def apply(range : Range) =
    OclTestFunction("get_global_id", range)

  def apply() =
    OclTestFunction("get_global_id", ContinuousRange(0, get_global_size()))
}

object get_group_id {
  def apply(range : Range) =
    OclTestFunction("get_group_id", range)

  def apply() =
    OclTestFunction("get_group_id", ContinuousRange(0, get_num_groups()))
}

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

  @Test
  def issue01(): Unit = {
    val K = Var("K")
    val M = Var("M")
    val N = Var("N")

    val expr = K * M * N * 1 /^ 32 * 1 /^ 4096

    val substitutionMap = Map[ArithExpr, ArithExpr](K -> 512, M -> 2048, N -> 2048)

    val result = ArithExpr.substitute(expr, substitutionMap)

    assertEquals(Cst(16384), result)
  }

  // Test how an NotEvaluableException is thrown
  @Test
  def issue02(): Unit = {
    try {
      Var("M").eval
    } catch {
      case NotEvaluableException() => return
    }
    assert(false)
  }

  @Test def testRandom(): Unit = {

    for (a <- 1 to 10) {
      val re = rndExpr(3)
      print(re)

      val oriEval = re.evalDouble
      val sim = re

      val simEval = sim.evalDouble
      assertTrue(oriEval+" != "+simEval, math.abs(oriEval-simEval) <= 1.0/1000000.0)
    }
  }

  @Test def testSimplification(): Unit = {

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
    assertEquals(Cst(0), result)
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
    val i = Var(ContinuousRange(0, M))
    assertEquals(i, i % M)
  }

  @Test def modVarSubtract(): Unit = {
    val c = Cst(-1)
    val n = Var("n", StartFromRange(2))
    val x = Var("x", ContinuousRange(0, n))

    assertEquals(c + x, (c + x) % n)
  }

  @Test def unnecessaryMod(): Unit = {
    val c = Cst(-1)
    val n = Var("n", StartFromRange(2))
    val gl_id = Var("x", ContinuousRange(0, n))

    assertEquals((c + n + gl_id) % n,(((c + gl_id) % n) + n) % n)
  }

  @Test def unnecessaryModDifferentRange(): Unit = {
    val c = Cst(-1)
    val n = Var("n", StartFromRange(2))
    val start = get_global_id()
    val step = get_global_size()
    val gl_id = Var("x", RangeAdd(start, n, step))

    assertEquals((c + n + gl_id) % n,(((c + gl_id) % n) + n) % n)
  }

  @Test def modMultipleOf(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M + 2))

    //           =     (j * (M + 2) + i) % (M + 2) = i
    val actual = ((M * j) + (2 * j) + i) % (2 + M)
    assertEquals(i, actual)
  }

  @Test def modMultipleOfReverse(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M + 2))

    //            =     (j * (M + 2) + i) % (M + 2) = i
    val actual =  (i + (j * 2) + (M * j)) % (2 + M)
    assertEquals(i, actual)
  }

  @Test def divFactorizeAndSimplifyFraction(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M + 2))

    val actual = ((M * j) + (2 * j) + i) / (2 + M)
    assertEquals(j, actual)
  }

  @Test def modTransposeTwicePadColumnValue(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M + 2))

    val actual = (((((M * j) + (2 * j) + i) % (2 + M)) + ((((M * j) + (2 * j) + i) / (2 + M)) * 2) +
                 ((((M * j) + (2 * j) + i) / (2 + M)) * M)) / (2 + M)) % N
    assertEquals(j, actual)
  }

  @Test def modTransposeTwicePadRowValue(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M + 2))

    val actual = (((((M * j) + (2 * j) + i) % (2 + M)) + ((((M * j) + (2 * j) + i) / (2 + M)) * 2) +
      ((((M * j) + (2 * j) + i) / (2 + M)) * M)) % (2 + M)) +
      (((((M * j) + (2 * j) + i) % (2 + M)) + ((((M * j) + (2 * j) + i) / (2 + M)) * 2) +
        ((((M * j) + (2 * j) + i) / (2 + M)) * M)) / ((N * M) + (2 * N)))
    assertEquals(i, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def modTransposeTwicePadFull(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M + 2))

    val actual = (((((((M * j) + (2 * j) + i) % (2 + M)) + ((((M * j) + (2 * j) + i) / (2 + M)) * 2) + ((((M * j) +
      (2 * j) + i) / (2 + M)) * M)) / (2 + M)) % N) +
      ((((((((((M * j) + (2 * j) + i) % (2 + M)) + ((((M * j) + (2 * j) + i) / (2 + M)) * 2) + ((((M * j) +
        (2 * j) + i) / (2 + M)) * M)) % (2 + M)) + (((((M * j) + (2 * j) + i) % (2 +     M)) +
        ((((M * j) + (2 * j) + i) / (2 + M)) * 2) + ((((M * j) + (2 * j) + i) / (2 + M)) * M)) / ((N * M) +
        (2 * N))) + -1) % M) + M) % M) * N))
    val gold = (((((-1 + i) % M) + M) % M) * N) + j
    assertEquals(gold, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def simpleFactorizationSimplification(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))

    val actual = ((2*N)+(M*N)) / (2+M)
    assertEquals(N, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def modTransposePadTransposePadPart(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))

    val actual = (((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) +
      ((((2 * i) + (i * N) + j) % (2 + N)) * M)) % (2 + M))
    assertEquals(i, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart1(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))

    val actual = (((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) +
      (i * N) + j) % (2 + N)) * M)) / (2 + M))
    assertEquals(j, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart2(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))

    val actual = (((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) +
      (i * N) + j) % (2 + N)) * M)) % (2 + M)) + ((((((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) +
      j) % (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) * M)) / (2 + M)) + -1)     % (((N * M) + (2 * N)) /
      (2 + M))) + (((N * M) + (2 * N)) / (2 + M))) % (((N * M) + (2 * N)) / (2 + M))) * M) + ((((((((((2 * i) +
      (i * N) + j) / (2     + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) *
      M)) / (2 + M)) + -1) % (((N * M) + (2 * N)) / (2 + M))) + (((N * M) + (2 * N)) / (2 + M))) % (((N * M) +
      (2 * N)) / (2 + M))) * 2)) / (2 + M))
    assertEquals((((j-1) % N) + N) % N, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart3(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))

    val actual = (((((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) +
      (i * N) + j) % (2 + N)) * M)) / (2 + M)) + -1) % (((N * M) + (2 * N)) / (2 + M))) + (((N * M) + (2 * N)) /
      (2 + M))) % (((N * M) + (2 * N)) / (2 + M)))
    assertEquals((((j-1) % N) + N) % N, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart4(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))

    val actual = ((((((-1 + j) % N) + N) % N) + ((((((((-1 + j) % N) + N) % N) * 2) +
      (((((-1 + j) % N) + N) % N) * M) + i) % (2 + M)) * N)) % N)
    assertEquals((((j-1) % N) + N) % N, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart5(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))
    val actual = (((((((-1 + j) % N) + N) % N) * 2) + (((((-1 + j) % N) + N) % N) * M) + i) % (2 + M))
    assertEquals(i, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart6(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))
    val actual = ((((((-1 + j) % N) + N) % N) + (i * N)) % N)
    assertEquals((((j-1) % N) + N) % N, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart7(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))
    val actual = (((((-1 + j) % N) + N) % N) / N)
    assertEquals(Cst(0), actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart8(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))
    val actual = ((((((((j-1) % N )+ N) % N) * M) + (((((j-1) % N) + N) % N)*2)+i)) / (((M*N)+(2*N))))
    assertEquals(Cst(0), actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart9(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))
    val actual = (((M * j) + (4 * j) + i) / (4 + M))
    assertEquals(j, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart10(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))
    val actual = (((4*i)+(i*N)+j)) / ((4+N))
    assertEquals(i, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPart11(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))
    val actual = (((((((-2 + j) % N) + N) % N) * 4) + (((((-2 + j) % N) + N) % N) * M) + i)) / ((4 + M))
    assertEquals((((j-2) % N) + N) % N, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def divTransposePadTransposePadPartFull(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M + 2))
    val actual = ((((((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) +
      (i * N) + j) % (2 + N)) * M)) % (2 + M)) + ((((((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) +
      j) % (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) * M)) / (2 + M)) + -1) % (((N * M) + (2 * N)) /
      (2 + M))) + (((N * M) + (2 * N)) / (2 + M))) % (((N * M) + (2 * N)) / (2 + M))) * M) + ((((((((((2 * i) +
      (i * N) + j) / (2 + N)    ) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) *
      M)) / (2 + M)) + -1) % (((N * M) + (2 * N)) / (2 + M))) + (((N * M) + (2 * N)) / (2 + M))) % (((N * M) +
      (2 * N)) / (2 + M))) * 2)) / (2 + M)) + ((((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) %
      (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) * M)) % (2 + M)) + ((((((((((2 * i) + (i * N) + j) /
      (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) * M)) / (2 + M)) +
      -1) % (((N * M) + (2 * N)) / (2 + M))) + (((N * M) + (2 * N)) / (2 + M))) % (((N * M) + (2 * N)) / (2 + M))) *
      M) + ((((((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) +
      (i * N) + j) % (2 + N)) * M)) / (2 + M)) + -1) % (((N * M) + (2 * N)) / (2 + M))) + (((N * M) + (2 * N)) /
      (2 + M))) % (((N * M) + (2 * N)) / (2 + M))) * 2)) % (2 + M)) * N)) % N) + ((((((((((((2 * i) + (i * N) + j) /
      (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) * M)) % (2 + M)) +
      ((((((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) +
      (i * N) + j) % (2 + N)) * M)) / (2 + M)) + -1) % (((N * M) + (2 * N)) / (2 + M))) + (((N * M) + (2 * N)) /
      (2 + M))) % (((N * M) + (2 * N)) / (2 + M))) * M) + ((((((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) +
      (i * N) + j) % (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) * M)) / (2 + M)) + -1) % (((N * M) +
      (2 * N)) / (2 + M))) + (((N * M) + (2 * N)) / (2 + M))) % (((N * M) + (2 * N)) / (2 + M))) * 2)) % (2 + M)) +
      (((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) + (i * N) +
      j) % (2 + N)) * M)) % (2 + M)) + ((((((((((2 * i) + (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) %
      (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) * M)) / (2 + M)) + -1) % (((N * M) + (2 * N)) /
      (2 + M))) + (((N * M    ) + (2 * N)) / (2 + M))) % (((N * M) + (2 * N)) / (2 + M))) * M) + ((((((((((2 * i) +
      (i * N) + j) / (2 + N)) + ((((2 * i) + (i * N) + j) % (2 + N)) * 2) + ((((2 * i) + (i * N) + j) % (2 + N)) *
      M)) / (2 + M)) + -1) % (((N * M) + (2 * N)) / (2 + M))) + (((N * M) + (2 * N)) / (2 + M))) % (((N * M) +
      (2 * N)) / (2 + M))) * 2)) / ((N * M) + (2 * N))) + -1) % M) + M) % M) * N))
    val gold = (((((-1 + j) % N) + N) % N) + (((((-1 + i) % M) + M) % M) * N))
    assertEquals(gold, actual)

  }

  @Test def slideTransposePadTransposePadPart1(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M))
    val k = Var("k", ContinuousRange(0, 3))
    val actual = ((N*i)+(N*k)+(2*i)+(2*k)+j) % (2+N)
    assertEquals(j, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideTransposePadTransposePadPart2(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M))
    val k = Var("k", ContinuousRange(0, 3))
    val actual = (((N * i) + (N * k) + (2 * i) + (2 * k) + j)) / ((2 + N))
    assertEquals(i+k, actual)
  }

  @Test def slideTransposePadTransposePadPart3(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M))
    val k = Var("k", ContinuousRange(0, 3))
    val actual = ((2*j)+(j*M)+k+i) % (2+M)
    assertEquals(i+k, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideTransposePadTransposePadPart4(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M))
    val k = Var("k", ContinuousRange(0, 3))
    val actual = (((2 * j) + (j * M) + k + i)) / ((2 + M))
    assertEquals(j, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideTransposePadTransposePadPart5(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M))
    val k = Var("k", ContinuousRange(0, 3))
    val actual =((((((-1 + j) % (N)) + N) % (N)) * 2) + (((((-1 + j) % (N)) + N) % (N)) * M) + k + i) % (2 + M)
    assertEquals(k+i, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideTransposePadTransposePadPart6(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M))
    val k = Var("k", ContinuousRange(0, 3))
    val actual = (((((((-1 + j) % (N)) + N) % (N)) * 2) + (((((-1 + j) % (N)) + N) % (N)) * M) + k + i)) / ((2 + M))
    assertEquals(((((-1 + j) % N) + N) % N), actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideTransposePadTransposePadPart7(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N + 2))
    val i = Var("i", ContinuousRange(0, M))
    val k = Var("k", ContinuousRange(0, 3))
    val actual = (((((-1 + j) % (N)) + N) % (N)) + (N * i) + (N * k)) % N
    assertEquals(((((-1 + j) % N) + N) % N), actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart1(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (((((-1 + j) % (N)) + N) % (N)) + (N * i)) % N
    assertEquals(((((-1 + j) % N) + N) % N), actual)
  }

  @Test def slideSlideTransposePadTransposePadPart2(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (1+(N*i)+(2*i)+j) % (2+N)
    assertEquals(j+1, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart3(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((1 + (N * i) + (2 * i) + j)) / ((2 + N))
    assertEquals(i, actual)
  }

  @Test def slideSlideTransposePadTransposePadPart4(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (2 + (M * j) + (2 * j) + M + i) % (2 + M)
    assertEquals(i, actual)
  }

  @Test def slideSlideTransposePadTransposePadPart5(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (2 + (M * j) + (2 * j) + M + i) / (2 + M)
    assertEquals(j + 1, actual)
  }

  @Test def slideSlideTransposePadTransposePadPart6(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (4 + (M * j) + (2 * j) + (2 * M) + i) % (2 + M)
    assertEquals(i, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart7(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (4 + (M * j) + (2 * j) + (2 * M) + i) / (2 + M)
    assertEquals(j+2, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart8(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((2 + N + j)) / ((2 + N))
    assertEquals(Cst(1), actual)
  }

  @Test def slideSlideTransposePadTransposePadPart9(): Unit = {
    val M = SizeVar("M")
    val N = Var("N", StartFromRange(2))
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    assertTrue(ArithExpr.isSmaller(AbsFunction(j-1),N).getOrElse(false))
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart10(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((2 + N + j) % ((2 + N)))
    assertEquals(j, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart11(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (1 + (((-1 + N + j) % (N)) * 2) + (((-1 + N + j) % (N)) * M) + i) % (2 + M)
    assertEquals(i + 1, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart12(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((1 + (((-1 + N + j) % (N)) * 2) + (((-1 + N + j) % (N)) * M) + i)) / ((2 + M))
    assertEquals((-1 + N + j) % (N), actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart13(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((3 + N + j)) / ((2 + N))
    assertEquals(Cst(1), actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart14(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((3 + N + j)) % ((2 + N))
    assertEquals(1+j, actual)
  }

  @Test def slideSlideTransposePadTransposePadPart15(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (3 + (N * i) + (2 * i) + N + j) % (2 + N)
    assertEquals(1+j, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart16(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (4 + i + (M * j) + (2 * j) + (2 * M)) % (2 + M)
    assertEquals(i, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart17(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((3 + N + j + (2 * i) + (N * i))) / ((2 + N))
    assertEquals(i+1, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart18(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (4 + N + j + (2 * i) + (N * i)) % (2 + N)
    assertEquals(j+2, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart19(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((4 + N + j + (2 * i) + (N * i))) / ((2 + N))
    assertEquals(i+1, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart20(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (5 + i + (2 * M) + (2 * j) + (M * j)) % (2 + M)
    assertEquals(i+1, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart21(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((5 + i + (2 * M) + (2 * j) + (M * j))) / ((2 + M))
    assertEquals(j+2, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart22(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (4 + j + (2 * N)) % ((2 + N))
    assertEquals(j, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart23(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = (5 + j + (2 * N)) % ((2 + N))
    assertEquals(j+1, actual)
  }

  //noinspection ScalaUnnecessaryParentheses
  @Test def slideSlideTransposePadTransposePadPart24(): Unit = {
    val M = SizeVar("M")
    val N = SizeVar("N")
    val j = Var("j", ContinuousRange(0, N))
    val i = Var("i", ContinuousRange(0, M))
    val actual = ((4 + j + (2 * N))) / ((2 + N))
    assertEquals(Cst(2), actual)
  }

  @Test def checkOrderOfTerms(): Unit = {
    val M = Var("v_M_177") // M < j in ascii
    val j = Var("v_j_179")
    assertTrue(ArithExpr.sort(M, j))
  }

  @Test def checkOrderOfTerms2(): Unit = {
    assertFalse(ArithExpr.sort(Cst(2), Cst(2)))
  }

  @Test def modOfVarWithConstantRange(): Unit = {
    val c =  Cst(10)
    val i = Var(ContinuousRange(0,c))
    assertEquals(i, i % c)
  }

  @Test def DivModOfVarWithConstantRange(): Unit = {
    val c =  Cst(10)
    val i = Var(ContinuousRange(0,c))

    assertEquals(Cst(0), (i % c) / Cst(20))
  }

  @Test def modOfVarWithConstantRange2(): Unit = {
    val i = Var(ContinuousRange(0, Cst(10)))
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
    val v_M_1 = SizeVar("v_M_1")
    val v_K_2 = SizeVar("v_K_2")
    val v_wg_id_39 = Var("v_wg_id_39", ContinuousRange(0,v_M_1 /^ 16))
    val v_l_id_30 = Var("v_l_id_30", ContinuousRange(0,8))
    val v_l_id_29 = Var("v_l_id_29", ContinuousRange(0,16))
    val v_i_27 = Var("v_i_27", ContinuousRange(0,1))
    val v_i_35 = Var("v_i_35", ContinuousRange(0,v_K_2 /^ 8))

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

  @Test def OneByOne(): Unit = {
    assertEquals(Cst(1), Cst(1) /^ Cst(1))
  }

  @Test def NByN(): Unit = {
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

  @Test def testIsSmallerVar(): Unit = {
    val n = SizeVar("N")

    assert(ArithExpr.isSmaller(n/^2,n).get)
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
    val a = SizeVar("a")
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
    import lift.arithmetic.ArithExpr.Math._

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
    import lift.arithmetic.ArithExpr.Math._

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
  def testIsSmaller(): Unit = {
    val i = Var("i", ContinuousRange(0, 2))
    val id = Var("id", ContinuousRange(0, 5))
    assert(!ArithExpr.isSmaller(id + 4*i, 8).getOrElse(false))
  }


  @Test
  def bugAIsSmaller(): Unit = {
    val i = Var("i", ContinuousRange(0, 2))
    val id = Var("id", ContinuousRange(0, 5))

    val expr1 = (id + 4*i) / 8

    // 0 <= id + 4*i <= 8 < 9
    assertNotEquals(Cst(0), expr1)
    assertNotEquals(id + 4*i, (id + 4*i) % 8)
  }

  @Test
  def bugBIsSmaller(): Unit = {
    val n = SizeVar("N")
    val l = Var("l", ContinuousRange(0, 4))

    assertTrue(ArithExpr.isSmaller(l * n/^4, n).get)
  }

  @Test
  def bugCIsSmaller(): Unit = {
    val a = Var("a")
    val c = Var("c")

    // a * -1 < c   should be unknown
    assert( ArithExpr.isSmaller(a * -1, c).isEmpty )
  }
  
  @Test
  def signCeil(): Unit = {
    val i = Var("i", ContinuousRange(0, 16))
    // ⌈x⌉ = 0  if  -1 < x ≤ 0
    assertEquals(Sign.Positive, CeilingFunction(Cst(1) * i /^ 16).sign)
  }
  
  @Test
  def annoyingWarning(): Unit = {
    val i = Var(RangeAdd(1, PosInf, 1))
    val j = Var(RangeAdd(0, i, 1))
    val x = (-1 * j * 1 /^ i) + (Cst(128) * 1 /^ i)
  
    assertEquals(Sign.Positive, CeilingFunction(x).sign)
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

    assertTrue(ArithExpr.isSmaller(l / 16, 8).get)
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

  @Ignore
  @Test
  def ceilNotSimplifying(): Unit = {
    val v_3_6 = SizeVar("")
    val v_2_5 = SizeVar("")

    // The Var's maximum value + 1 is the inverse of it's multiplier

    // v_3_6 > v_2_5
    val expr1 = ceil(1 + (-1 * 8 * Var("", RangeAdd(0, Cst(64) /^ 8, 1)) * 1 /^ 64))
    // v_3_6 < v_2_5
    val expr2 = ceil(1 + (-1 * 64 * Var("", RangeAdd(0, Cst(8) /^ 64, 1)) * 1 /^ 8))
    // v_3?6 == v_2_5
    val expr3 = ceil(1 + (-1 * 64 * Var("", RangeAdd(0, Cst(64) /^ 64, 1)) * 1 /^ 64))

    val expr4 = ceil(1 + (-1 * v_2_5 * Var("", RangeAdd(0, v_3_6 * 1 /^ v_2_5, 1)) * 1 /^ v_3_6))

    assertEquals(Cst(1), expr1)
    assertEquals(Cst(1), expr2)
    assertEquals(Cst(1), expr3)
    assertEquals(Cst(1), expr4)
  }

  @Test
  def numValsNotSimplifying(): Unit = {
    val M = SizeVar("M")
    val p = SizeVar("p")
    val rangeStart = Var("get_group_id", RangeAdd(0, M/^p, 1))

    val range = RangeAdd(rangeStart, M /^ p, M/^ p)

    assertEquals(Cst(1), range.numVals)
  }

  @Test
  def numValsNotSimplifying2(): Unit = {
    val M = SizeVar("M")
    val p = SizeVar("p")
    val rangeStart = get_group_id(RangeAdd(0, M/^p, 1))

    val range = RangeAdd(rangeStart, M /^ p, M/^ p)

    assertEquals(Cst(1), range.numVals)
  }

  @Test
  def rangeMinMax(): Unit = {
    val range = RangeAdd(0, Cst(8) /^ 64, 1)
    assertTrue(range.min.evalDouble <= range.max.evalDouble)
    assertTrue(range.max.evalDouble >= 0)
  }

  @Ignore
  @Test def foo1(): Unit = {
    ceil(NegInf) % ?
  }
}
