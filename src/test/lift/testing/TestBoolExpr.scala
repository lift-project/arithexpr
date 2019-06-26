package lift.testing

import lift.arithmetic.BoolExpr.ArithPredicate
import lift.arithmetic._
import org.junit.Assert.assertEquals
import org.junit.Test

class TestComparison {
  import ArithPredicate.Operator
  @Test
  def equalsDecided = assertEquals(Some(true), ArithPredicate(1,1, Operator.==))

  @Test
  def equalsUndecided = assertEquals(None, ArithPredicate(1, 2, Operator.==))

  @Test
  def nonEqualsDecided = assertEquals(Some(false), ArithPredicate(1,1, Operator.!=))

  @Test
  def nonEqualsUndecided = assertEquals(None, ArithPredicate(1, 2, Operator.!=))
  
  @Test
  def isLT = assertEquals(Some(true), ArithPredicate(1,2, Operator.<))

  @Test
  def nonLT = assertEquals(Some(false), ArithPredicate(1,1), Operator.<)

  @Test
  def undecidedLT = assertEquals(None, ArithPredicate(NamedVar("x"), NamedVar("y"), Operator.<))

  @Test
  def isLTE = assertEquals(Some(true), ArithPredicate(1,1), Operator.<=)

  @Test
  def nonLTE = assertEquals(Some(false), ArithPredicate(2, 1), Operator.<=)

  @Test
  def isGT = assertEquals(Some(true), ArithPredicate(2,1, Operator.>))

  @Test
  def nonGT = assertEquals(Some(false), ArithPredicate(1,1), Operator.>)

  @Test
  def undecidedGT = assertEquals(None, ArithPredicate(NamedVar("x"), NamedVar("y"), Operator.>))

  @Test
  def isGTE = assertEquals(Some(true), ArithPredicate(1,1), Operator.>=)

  @Test
  def nonGTE = assertEquals(Some(false), ArithPredicate(1, 2), Operator.>=)}
