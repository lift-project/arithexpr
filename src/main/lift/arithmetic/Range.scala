package lift
package arithmetic

import scala.collection.mutable.ListBuffer

sealed abstract class Range {
  // default impl
  def *(e: ArithExpr with SimplifiedExpr): Range = this
  // minimum value this range can take (note this is not recursive, if there is a var in the range somewhere, we do not try to take its minimum value
  val min : ArithExpr with SimplifiedExpr
  // maximum value this range can take
  val max : ArithExpr with SimplifiedExpr

  def digest(): Int = min.digest() ^ max.digest()

  override def equals(that: Any): Boolean = that match {
    case r: Range => this.min == r.min && this.max == r.max
    case _ => false
  }

  def equalsStructurally(that: Range): Boolean = (this, that) match {
    case (ra1: RangeAdd, ra2: RangeAdd)             => ra1.start.equalsStructurally(ra2.start) &&
                                                        ra1.stop.equalsStructurally(ra2.stop) &&
                                                        ra1.step.equalsStructurally(ra2.step)
    case (rm1: RangeMul, rm2: RangeMul)             => rm1.start.equalsStructurally(rm2.start) &&
                                                        rm1.stop.equalsStructurally(rm2.stop) &&
                                                        rm1.mul.equalsStructurally(rm2.mul)
    case (rg1: GoesToRange, rg2: GoesToRange)       => rg1.`end`.equalsStructurally(rg2.`end`)
    case (rs1: StartFromRange, rs2: StartFromRange) => rs1.start.equalsStructurally(rs2.start)
    case _                                          => false
  }

  def visitAndRebuild(f: ArithExpr => ArithExpr): Range

  /* Number of different values this range can take */
  lazy val numVals: ArithExpr with SimplifiedExpr = ?
}

object Range {
  def unapply(r: Range): Option[(ArithExpr with SimplifiedExpr, ArithExpr with SimplifiedExpr)] = Some(r.min, r.max)

  def substitute(r: Range, substitutions: scala.collection.Map[ArithExpr, ArithExpr]): Range = {
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
  def printToScalaString(r: Range, printNonFixedVarIds: Boolean): String = r match {
    case StartFromRange(start) =>             s"StartFromRange(${ArithExpr.printToScalaString(start, printNonFixedVarIds)})"
    case GoesToRange(end) =>                  s"GoesToRange(${ArithExpr.printToScalaString(end, printNonFixedVarIds)})"
    case RangeAdd(start, stop, step) =>       s"RangeAdd(${ArithExpr.printToScalaString(start, printNonFixedVarIds)}, " +
                                                       s"${ArithExpr.printToScalaString(stop, printNonFixedVarIds)}, " +
                                                       s"${ArithExpr.printToScalaString(step, printNonFixedVarIds)})"
    case RangeMul(start, stop, mul) =>        s"RangeMul(${ArithExpr.printToScalaString(start, printNonFixedVarIds)}, " +
                                                       s"${ArithExpr.printToScalaString(stop, printNonFixedVarIds)}, " +
                                                       s"${ArithExpr.printToScalaString(mul, printNonFixedVarIds)})"
    case RangeUnknown =>                      s"RangeUnknown"
    case _ =>
      throw new NotImplementedError(s"Range $r is not supported in printing Range to Scala notation String")
  }
}

class RangeUnknownException(msg: String) extends Exception(msg)

case class StartFromRange(start: ArithExpr with SimplifiedExpr) extends Range {
  override def *(e: ArithExpr with SimplifiedExpr): Range = {
    StartFromRange(start * e)
  }
  override val min: ArithExpr with SimplifiedExpr = start
  override val max: ArithExpr with SimplifiedExpr = PosInf

  override def equals(that: Any): Boolean = that match {
    case r: StartFromRange => this.start == r.start
    case _ => false
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): Range =
    StartFromRange(start.visitAndRebuild(f))
}

case class GoesToRange(end: ArithExpr with SimplifiedExpr) extends Range {
  override def *(e: ArithExpr with SimplifiedExpr): Range = {
    GoesToRange(end * e)
  }
  override val min: ArithExpr with SimplifiedExpr = NegInf
  override val max: ArithExpr with SimplifiedExpr = end-1

  override def equals(that: Any): Boolean = that match {
    case r: GoesToRange => this.end == r.end
    case _ => false
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): Range =
    GoesToRange(end.visitAndRebuild(f))
}

case class RangeAdd(start: ArithExpr with SimplifiedExpr,
                    stop: ArithExpr with SimplifiedExpr,
                    step: ArithExpr with SimplifiedExpr) extends Range {

  override def *(e: ArithExpr with SimplifiedExpr): Range = {
    RangeAdd(start * e, stop * e, step)
  }

  private def checkBound(up: Boolean, result: ArithExpr with SimplifiedExpr): ArithExpr with SimplifiedExpr = {
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
  
  override val min: ArithExpr with SimplifiedExpr = {
    if (step.sign == Sign.Negative)
      checkBound(up=false, stop + 1)
    else
      start
  }
  override val max: ArithExpr with SimplifiedExpr = {
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

  override lazy val numVals: ArithExpr with SimplifiedExpr = {
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

  def includedIn(other: RangeAdd): Boolean = {
    if (ArithExpr.isSmaller(this.stop, other.start).getOrElse(true) || this.stop == other.start)
      return false

    if (ArithExpr.isSmaller(other.stop, this.start).getOrElse(true) || other.stop == this.start)
      return false

    other.step % this.step == Cst(0) &&
      abs(this.start - other.start) % this.step == Cst(0)
  }

  def includedIn(others: List[RangeAdd]): Boolean = others.exists(other => this.includedIn(other))
}

object RangeAdd {
  def flattenContinuousTermRanges(sumTermRanges: List[RangeAdd]): List[RangeAdd] = {
    val updatedRanges = ListBuffer[RangeAdd](sumTermRanges: _*)

    def mergeWithOneOfUpdatedRanges(thisRange: RangeAdd,
                                    thisRangeIdx: Int): Boolean = {
      updatedRanges.zipWithIndex.foreach {
        case (otherRange, otherRangeIdx) if otherRange != thisRange =>
          val merged = merge(thisRange, otherRange)
          if (merged.isDefined) {
            updatedRanges.remove(otherRangeIdx)
            updatedRanges.insert(otherRangeIdx, merged.get)
            updatedRanges.remove(thisRangeIdx)
            return true
          }
        case _ =>
      }
      false
    }

    def flattenAPairIfPossible(): Boolean = {
      updatedRanges.zipWithIndex.foreach(range =>
        if (mergeWithOneOfUpdatedRanges(range._1, range._2))
          return true)
      false
    }

    var flattenAgain = true
    while (flattenAgain)
      flattenAgain = flattenAPairIfPossible()

    updatedRanges.toList
  }

  def merge(r1: RangeAdd, r2: RangeAdd): Option[RangeAdd] = {

    def aCoversIntervalsOfB(rA: RangeAdd, rB: RangeAdd): Boolean =
      rA.start == rB.start &&
        // Steps overlap and rA.step >= rB.step
        rA.step % rB.step == Cst(0) &&
        // Range rA covers the whole interval between the steps of range rB
        (rA.step == rB.stop || ArithExpr.isSmaller(rA.step, rB.stop).getOrElse(false))

    // [0, 3, 6] + [0, 1, 2] = [0, 1, 2, 3, 4, 6, 7, 8]
    if (aCoversIntervalsOfB(rA=r1, rB=r2))
      Some(RangeAdd(r1.start, ArithExpr.max(r1.stop, r2.stop), r2.step))

    // [0, 1, 2] + [0, 3, 6] = [0, 1, 2, 3, 4, 6, 7, 8]
    else if (aCoversIntervalsOfB(rA=r2, rB=r1))
      Some(RangeAdd(r1.start, ArithExpr.max(r1.stop, r2.stop), r1.step))

    else None
  }
}

case class RangeMul(start: ArithExpr with SimplifiedExpr,
                    stop: ArithExpr with SimplifiedExpr,
                    mul: ArithExpr with SimplifiedExpr) extends Range {
  override def *(e: ArithExpr with SimplifiedExpr): Range = {
    RangeMul(start * e, stop * e, mul)
  }
  override val min: ArithExpr with SimplifiedExpr = start
  override val max: ArithExpr with SimplifiedExpr = stop /^ mul

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
  override val min: ArithExpr with SimplifiedExpr = ?
  override val max: ArithExpr with SimplifiedExpr = ?

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): Range = this
}
