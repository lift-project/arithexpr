package lift
package arithmetic

import lift.arithmetic.simplifier.ExprSimplifier

sealed abstract class Range {
  // default impl
  def *(e: ArithExpr): Range = this
  val min : ArithExpr // minimum value this range can take (note this is not recursive, if there is a var in the range somewhere, we do not try to take its minimum value
  val max : ArithExpr // maximum value this range can take

  def digest(): Int = min.digest() ^ max.digest()

  override def equals(that: Any): Boolean = that match {
    case r: Range => this.min == r.min && this.max == r.max
    case _ => false
  }

  def visitAndRebuild(f: ArithExpr => ArithExpr): Range

  /* Number of different values this range can take */
  lazy val numVals: ArithExpr = ?
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

  /**
    * Converts a Range to a Scala notation String which can be evaluated into a valid Range
    */
  def printToScalaString(r: Range): String = r match {
    case StartFromRange(start) =>             s"StartFromRange(${ArithExpr.printToScalaString(start)}"
    case GoesToRange(end) =>                  s"GoesToRange(${ArithExpr.printToScalaString(end)}"
    case RangeAdd(start, stop, step) =>       s"RangeAdd(${ArithExpr.printToScalaString(start)}, " +
                                                       s"${ArithExpr.printToScalaString(stop)}, " +
                                                       s"${ArithExpr.printToScalaString(step)})"
    case RangeMul(start, stop, mul) =>        s"RangeMul(${ArithExpr.printToScalaString(start)}, " +
                                                       s"${ArithExpr.printToScalaString(stop)}, " +
                                                       s"${ArithExpr.printToScalaString(mul)})"
    case RangeUnknown =>                      s"RangeUnknown"
    case r =>
      throw new NotImplementedError(s"Range $r is not supported in printing Range to Scala notation String")
  }
}

class RangeUnknownException(msg: String) extends Exception(msg)

case class StartFromRange(start: ArithExpr) extends Range {
  override def *(e: ArithExpr): Range = {
    StartFromRange(ExprSimplifier(start * e))
  }
  override val min: ArithExpr = start
  override val max: ArithExpr = PosInf

  override def equals(that: Any): Boolean = that match {
    case r: StartFromRange => this.start == r.start
    case _ => false
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): Range =
    StartFromRange(start.visitAndRebuild(f))
}

case class GoesToRange(end: ArithExpr) extends Range {
  override def *(e: ArithExpr): Range = {
    GoesToRange(ExprSimplifier(end * e))
  }
  override val min: ArithExpr = NegInf
  override val max: ArithExpr = end-1

  override def equals(that: Any): Boolean = that match {
    case r: GoesToRange => this.end == r.end
    case _ => false
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): Range =
    GoesToRange(end.visitAndRebuild(f))
}

case class RangeAdd(start: ArithExpr, stop: ArithExpr, step: ArithExpr) extends Range {
  override def *(e: ArithExpr): Range = {
    RangeAdd(ExprSimplifier(start * e), ExprSimplifier(stop * e), step)
  }

  private def checkBound(up: Boolean, result: ArithExpr)
                        : ArithExpr = {
    try {
      val evaluatedResult = result.evalDouble
      val evaluatedStart = start.evalDouble

      if ((evaluatedResult < evaluatedStart) != up)
        result
      else
        // Fall back on `start` is `result` is out of bounds
        start
    } catch {
      case NotEvaluableException() => result
    }
  }
  
  override val min: ArithExpr = {
    if (step.sign == Sign.Negative)
      checkBound(up=false, stop + 1)
    else
      start
  }
  override val max: ArithExpr = {
    if (step.sign == Sign.Positive)
      // TODO: this maximum is too high! consider the following range: RangeAdd(0,10,5) in which case the max is 5, not 9
      checkBound(up=true, stop - 1)
    else
      start
  }

  override def equals(that: Any): Boolean = that match {
    case r: RangeAdd => this.start == r.start && this.stop == r.stop && this.step == r.step
    case _ => false
  }

  override lazy val numVals: ArithExpr = {
    // TODO: Workaround. See TestExpr.numValsNotSimplifying
    // TODO: and TestExpr.ceilNotSimplifying
    if ((
          ArithExpr.isSmaller(start, stop).getOrElse(false) &&
          ArithExpr.isSmaller(max, start + step).getOrElse(false)) ||
        (
          ArithExpr.isSmaller(stop, start).getOrElse(false) &&
          ArithExpr.isSmaller(start + step, min).getOrElse(false)))
      Cst(1)
    else {
      if (this.step.sign == Sign.Positive)
        ceil((this.stop - this.start) /^ this.step)
      else
        ceil((this.start - this.stop) /^(-1 * this.step))
    }
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): Range =
    RangeAdd(start.visitAndRebuild(f), stop.visitAndRebuild(f), step.visitAndRebuild(f))
}

case class RangeMul(start: ArithExpr, stop: ArithExpr, mul: ArithExpr) extends Range {
  override def *(e: ArithExpr): Range = {
    RangeMul(ExprSimplifier(start * e), ExprSimplifier(stop * e), mul)
  }
  override val min: ArithExpr = start
  override val max: ArithExpr = stop /^ mul

  override def equals(that: Any): Boolean = that match {
    case r: RangeMul => this.start == r.start && this.stop == r.stop && this.mul == r.mul
    case _ => false
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): Range =
    RangeMul(start.visitAndRebuild(f), stop.visitAndRebuild(f), mul.visitAndRebuild(f))
}

object ContinuousRange {
  def apply(start: ArithExpr, stop: ArithExpr): RangeAdd = {
    RangeAdd(start, stop, Cst(1))
  }
}

case object RangeUnknown extends Range {
  override val min: ArithExpr = ?
  override val max: ArithExpr = ?

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): Range = this
}
