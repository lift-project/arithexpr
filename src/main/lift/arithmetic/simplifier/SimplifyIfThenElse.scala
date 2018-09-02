package lift
package arithmetic
package simplifier

import com.sun.corba.se.spi.activation.NoSuchEndPoint

import scala.util.Try

object SimplifyIfThenElse {
  def simplify(test: Predicate, t : ArithExpr, e : ArithExpr): Option[ArithExpr] = {
    // If both branches are the same, it doesn't matter which one we take
    if (e == t) Some(t)
    // otherwise try to evaluate the predicate
    else {
      ExprSimplifier(test.lhs - test.rhs) match {
        case Cst(v) =>
          val op = test.op
          import lift.arithmetic.Predicate.Operator
          // true predicate
          if ((v > 0 && (op == Operator.> || op == Operator.>=)) ||
            (v < 0 && (op == Operator.< || op == Operator.<=)) ||
            (v == 0 && (op == Operator.== || op == Operator.<= || op == Operator.>=)) ||
            (v != 0 && op == Operator.!=)) Some(t)
          else Some(e)
        case _ =>
          if (alwaysTrue(test.lhs, test.rhs, test.op)) Some(t)
          else if (alwaysFalse(test.lhs, test.rhs, test.op)) Some(e)
          else None
      }
    }
  }

    def alwaysTrue(left:ArithExpr, right:ArithExpr, op:Predicate.Operator.Operator):Boolean = {
      val canonical = ExprSimplifier(left - right)

      op match {
        case Predicate.Operator.< =>
          canonical.atMax match {
            case NegInf => true
            case PosInf => false
            case other => Try(other.evalInt < 0).getOrElse(false)
          }
        case Predicate.Operator.<= =>
          canonical.atMax match {
            case NegInf => true
            case PosInf => false
            case other => Try(other.evalInt <= 0).getOrElse(false)
          }

        case Predicate.Operator.> =>
          canonical.atMin match {
            case NegInf => false
            case PosInf => true
            case other => Try(other.evalInt > 0).getOrElse(false)
          }
        case Predicate.Operator.>= =>
          canonical.atMin match {
            case NegInf => false
            case PosInf => true
            case other => Try(other.evalInt >= 0).getOrElse(false)
          }
        case _ => false
      }
    }

    def alwaysFalse(left:ArithExpr, right:ArithExpr, op:Predicate.Operator.Operator):Boolean = {
      val canonical = ExprSimplifier(left - right)

      op match {
        case Predicate.Operator.< =>
          canonical.atMin match {
            case NegInf => false
            case PosInf => true
            case other => Try(other.evalInt >= 0).getOrElse(false)
          }
        case Predicate.Operator.<= =>
          canonical.atMin match {
            case NegInf => false
            case PosInf => true
            case other => Try(other.evalInt > 0).getOrElse(false)
          }

        case Predicate.Operator.> =>
          canonical.atMax match {
            case NegInf => true
            case PosInf => false
            case other => Try(other.evalInt <= 0).getOrElse(false)
          }
        case Predicate.Operator.>= =>
          canonical.atMax match {
            case NegInf => true
            case PosInf => false
            case other => Try(other.evalInt < 0).getOrElse(false)
          }
        case _ => false
      }
    }

  def apply(test: Predicate, t : ArithExpr, e : ArithExpr): ArithExpr = {

  import scala.util.Try

  val simplificationResult = if (PerformSimplification()) simplify(test, t, e) else None
    simplificationResult match {
      case Some(toReturn) => toReturn
      case None => new IfThenElse(Predicate(ExprSimplifier(test.lhs), ExprSimplifier(test.rhs), test.op), ExprSimplifier(t), ExprSimplifier(e)) with SimplifiedExpr
    }
  }
}
