package lift.arithmetic.simplifier

import lift.arithmetic.{?, ArithExpr, OpaqueVar, PerformSimplification, Range, RangeUnknown, SimplifiedExpr, Var}

object SimplifyVar {

  def simplify(name: String, r: Range, fixedId: Option[Long]): Option[ArithExpr with SimplifiedExpr] = {
    if (r.min != ? && r.min == r.max) Some(r.min)
    else None
  }

  def apply(name: String = "", r: Range = RangeUnknown, fixedId: Option[Long] = None): ArithExpr with SimplifiedExpr = {
    val simplificationResult = if (PerformSimplification()) simplify(name, r, fixedId) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None => new Var(name, r, fixedId) with SimplifiedExpr
    }
  }

  def apply(v: Var): ArithExpr with SimplifiedExpr = {
    val simplificationResult = if (PerformSimplification()) simplify(v.name, v.range, Some(v.id)) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None =>
        v match {
          // Recreate OpaqueVar with the simplified trait
          case oV: OpaqueVar => new OpaqueVar(oV.v, oV.range, Some(oV.id)) with SimplifiedExpr
          // N.B. all new concrete Var subtypes have to be processed here separately
          case _ => new Var(v.name, v.range, Some(v.id)) with SimplifiedExpr
      }
    }
  }
}
