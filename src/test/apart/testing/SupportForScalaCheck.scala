package apart.testing

import apart.arithmetic._
import apart.arithmetic.simplifier._
import org.scalacheck._
import Gen._
import Arbitrary.arbitrary

object SupportForScalaCheck {
  val maxSizeOfSumsAndProducts = 10
  val maxNestingDepth = 10

  // Predicate
  def genPredicateOperator: Gen[Predicate.Operator.Value] =
    Gen.oneOf(
      Predicate.Operator.<,
      Predicate.Operator.>,
      Predicate.Operator.<=,
      Predicate.Operator.>=,
      Predicate.Operator.!=,
      Predicate.Operator.==)

  def genPredicate(level: Int): Gen[Predicate] = for {
    lhs <- genArithExprTree(level)
    rhs <- genArithExprTree(level)
    op <- genPredicateOperator
  } yield Predicate(lhs, rhs, op)

  // Range
  def genStartFromRange(level: Int): Gen[StartFromRange] = for {
    start <- genArithExprTree(level)
  } yield StartFromRange(start)

  def genGoesToRange(level: Int): Gen[GoesToRange] = for {
    end <- genArithExprTree(level)
  } yield GoesToRange(end)

  def genRangeAdd(level: Int): Gen[RangeAdd] = for {
    start <- genArithExprTree(level)
    stop <- genArithExprTree(level)
    step <- genArithExprTree(level)
    if step.sign == Sign.Positive
    if stop.sign == Sign.Positive | start.sign == Sign.Positive
  } yield RangeAdd(start, stop, step)

  def genRangeMul(level: Int): Gen[RangeMul] = for {
    start <- genArithExprTree(level)
    stop <- genArithExprTree(level)
    mul <- genArithExprTree(level)
  } yield RangeMul(start, stop, mul)

  def genRangeUnknown: Gen[RangeUnknown.type] = const(RangeUnknown)

  def genRange(level: Int): Gen[Range] =
    Gen.oneOf(
      genStartFromRange(level),
      genGoesToRange(level),
      genRangeAdd(level),
      genRangeMul(level),
      genRangeUnknown)

  // ArithExpr

  def `gen?` = const(?)

  def genPosInf = const(PosInf)

  def genNegInf = const(NegInf)

  def genCst = for {
    c <- arbitrary[Int]
  } yield Cst(c)

  def leafes = Gen.oneOf(`gen?`, genPosInf, genNegInf, genCst, genPosVar, genSizeVar)

  def genIntDiv(level: Int) = Gen.lzy(for {
    numer <- genArithExprTree(level)
    denom <- genArithExprTree(level)
  } yield SimplifyIntDiv(numer, denom))

  def genPow(level: Int) = Gen.lzy(for {
    b <- genArithExprTree(level)
    e <- genArithExprTree(level)
  } yield SimplifyPow(b, e))

  def genLog(level: Int) = Gen.lzy(for {
    b <- genArithExprTree(level)
    x <- genArithExprTree(level)
  } yield Log(b, x))

  def genProd(level: Int) = Gen.lzy(
    Gen.choose(2, maxSizeOfSumsAndProducts) flatMap { size =>
      Gen.listOfN(size, genArithExprTree(level)).map(l => ExprSimplifier(Prod(l)))
    })

  def genSum(level: Int) = Gen.lzy(
    Gen.choose(2, maxSizeOfSumsAndProducts) flatMap { size =>
      Gen.listOfN(size, genArithExprTree(level)).map(l => ExprSimplifier(Prod(l)))
    })

  def genMod(level: Int) = Gen.lzy(for {
    dividend <- genArithExprTree(level)
    divisor <- genArithExprTree(level)
  } yield SimplifyMod(dividend, divisor))

  def genAbs(level: Int) = Gen.lzy(for {
    ae <- genArithExprTree(level)
  } yield SimplifyAbs(ae))

  def genFloor(level: Int) = Gen.lzy(for {
    ae <- genArithExprTree(level)
  } yield SimplifyFloor(ae))

  def genCeiling(level: Int) = Gen.lzy(for {
    ae <- genArithExprTree(level)
  } yield SimplifyCeiling(ae))

  def genIfThenElse(level: Int) = Gen.lzy(for {
    test <- genPredicate(level)
    t <- genArithExprTree(level)
    e <- genArithExprTree(level)
  } yield SimplifyIfThenElse(test, t, e))

  def genArithExprFunction(level: Int) = Gen.lzy(for {
    name <- arbitrary[String]
    range <- genRange(level)
  } yield ArithExprFunction(name, range))

  def genLookup(level: Int) = Gen.lzy(for {
    id <- arbitrary[Int]
    table <- Gen.sized { size => Gen.listOfN(size, genArithExprTree(level)) }
    index <- genArithExprTree(level)
    if id < table.length
  } yield Lookup(table, index, id))

  def genRandomVar(level: Int) = Gen.lzy(for {
    name <- arbitrary[String]
    range <- genRange(level)
  } yield Var(name, range))

  def genPosVar = for {
    name <- arbitrary[String]
  } yield PosVar(name)

  def genSizeVar = for {
    name <- arbitrary[String]
  } yield SizeVar(name)

  def genNode(level: Int): Gen[ArithExpr] = Gen.lzy(Gen.oneOf(
    genIntDiv(level),
    genPow(level),
    genLog(level),
    genProd(level),
    genSum(level),
    genMod(level),
    genAbs(level),
    genFloor(level),
    genCeiling(level),
    genIfThenElse(level),
    genArithExprFunction(level),
    genLookup(level),
    genRandomVar(level)
  ))

  def genArithExprTree(level: Int) : Gen[ArithExpr] = {
    if (level >= maxNestingDepth) { leafes }
    else { Gen.oneOf(leafes, genNode(level + 1)) }
  }

  def genArithExpr: Gen[ArithExpr] = genArithExprTree(0)

  implicit val arbArithExpr: Arbitrary[ArithExpr] = Arbitrary(genArithExpr)
}
