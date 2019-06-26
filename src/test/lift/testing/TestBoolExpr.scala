package lift.testing

import lift.arithmetic.BoolExpr.ArithPredicate
import lift.arithmetic._
import org.junit.Assert.assertEquals
import org.junit.Test

class TestBoolExpr {
  import ArithPredicate.{Operator => Op}
  import ArithPredicate.Operator.Operator

  def assertPredicate(lhs: ArithExpr, op: Operator, rhs: ArithExpr, result: Option[Boolean]): Unit = {
    assertEquals(result, ArithPredicate(lhs, rhs, op).evaluate)
  }

  @Test
  def equalsDecided = assertPredicate(1, Op.==, 1, Some(true))

  @Test
  def equalsUndecided = assertPredicate(1, Op.==, 2, None)

  @Test
  def nonEqualsDecided = assertPredicate(1, Op.!=, 1, Some(false))

  @Test
  def nonEqualsUndecided = assertPredicate(1, Op.!=, 2, None)
  
  @Test
  def isLT = assertPredicate(1, Op.<, 2, Some(true))

  @Test
  def nonLT = assertPredicate(1, Op.<, 1, Some(false))

  @Test
  def undecidedLT = assertPredicate(NamedVar("x"), Op.<, NamedVar("y"), None)

  @Test
  def isLTE = assertPredicate(1, Op.<=, 1, Some(true))

  @Test
  def nonLTE = assertPredicate(2, Op.<=, 1, Some(false))

  @Test
  def isGT = assertPredicate(2, Op.>, 1, Some(true))

  @Test
  def nonGT = assertPredicate(1, Op.>, 1, Some(false))

  @Test
  def undecidedGT = assertPredicate(NamedVar("x"), Op.>, NamedVar("y"), None)

  @Test
  def isGTE = assertPredicate(1, Op.>=, 1, Some(true))

  @Test
  def nonGTE = assertPredicate(1, Op.>=, 2, Some(false))
}
