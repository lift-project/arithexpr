package apart
package arithmetic

import arithmetic.simplifier.ExprSimplifier

sealed abstract class Range {
  // default impl
  def *(e: ArithExpr): Range = this
  val min : ArithExpr // minimum value this range can take (note this is not recursive, if there is a var in the range somewhere, we do not try to take its minimum value
  val max : ArithExpr // maximum value this range can take

  def digest() = min.digest() ^ max.digest()

  override def equals(that: Any) = that match {
    case r: Range => this.min == r.min && this.max == r.max
    case _ => false
  }

  /* Number of different values this range can take */
  lazy val numVals : ArithExpr = ?
}

object Range {
  def substitute(r: Range, substitutions: scala.collection.Map[ArithExpr,ArithExpr]) : Range = {
    r match {
      case s: StartFromRange => StartFromRange(ArithExpr.substitute(s.start, substitutions))
      case g: GoesToRange => GoesToRange(ArithExpr.substitute(g.end, substitutions))
      case a: RangeAdd => RangeAdd(ArithExpr.substitute(a.start, substitutions),ArithExpr.substitute(a.stop, substitutions),ArithExpr.substitute(a.step, substitutions))
      case m: RangeMul => RangeMul(ArithExpr.substitute(m.start, substitutions),ArithExpr.substitute(m.stop, substitutions),ArithExpr.substitute(m.mul, substitutions))
      case RangeUnknown => r
    }
  }
}

class RangeUnknownException(msg: String) extends Exception(msg)

case class StartFromRange(start: ArithExpr) extends Range {
  override def *(e: ArithExpr): Range = {
    StartFromRange(ExprSimplifier(start * e))
  }
  override val min = start
  override val max = PosInf

  override def equals(that: Any) = that match {
    case r: StartFromRange => this.start == r.start
    case _ => false
  }
}

case class GoesToRange(end: ArithExpr) extends Range {
  override def *(e: ArithExpr): Range = {
    GoesToRange(ExprSimplifier(end * e))
  }
  override val min = NegInf
  override val max = end-1

  override def equals(that: Any) = that match {
    case r: GoesToRange => this.end == r.end
    case _ => false
  }
}

case class RangeAdd(start: ArithExpr, stop: ArithExpr, step: ArithExpr) extends Range {
  override def *(e: ArithExpr): Range = {
    RangeAdd(ExprSimplifier(start * e), ExprSimplifier(stop * e), step)
  }
  override val min = start
  override val max = {
    assert (step.sign == Sign.Positive)
    assert (stop.sign == Sign.Positive | start.sign == Sign.Positive)
    // TODO: this maximum is too high! consider the following range: RangeAdd(0,10,5) in which case the max is 5, not 9
    // also consider the case where the step is negative and the stop is also negative, this would break (hence the assertion)
    stop - 1
  }

  override def equals(that: Any) = that match {
    case r: RangeAdd => this.start == r.start && this.stop == r.stop && this.step == r.step
    case _ => false
  }

  override lazy val numVals : ArithExpr = ceil((this.stop - this.start) /^ this.step)

}

case class RangeMul(start: ArithExpr, stop: ArithExpr, mul: ArithExpr) extends Range {
  override def *(e: ArithExpr): Range = {
    RangeMul(ExprSimplifier(start * e), ExprSimplifier(stop * e), mul)
  }
  override val min = start
  override val max = stop /^ mul

  override def equals(that: Any) = that match {
    case r: RangeMul => this.start == r.start && this.stop == r.stop && this.mul == r.mul
    case _ => false
  }
}

object ContinuousRange {
  def apply(start: ArithExpr, stop: ArithExpr) = {
    RangeAdd(start, stop, Cst(1))
  }
}

case object RangeUnknown extends Range {
  override val min = ?
  override val max = ?
}
