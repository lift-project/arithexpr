package lift.arithmetic

import lift.arithmetic.BoolExpr.ArithPredicate.Operator.Operator
import lift.arithmetic.simplifier.ExprSimplifier

case class IfThenElseBuilder(test:BoolExpr, thenExpr:ArithExpr) {
  def !!(elseExpr:ArithExpr):IfThenElse = IfThenElse(test, thenExpr, elseExpr)
}

sealed trait BoolExpr {
  def digest:Int

  def visit(f:ArithExpr => Unit):Unit

  def visitAndRebuild(f:ArithExpr => ArithExpr):BoolExpr

  def simplifyInnerArithExpr:BoolExpr

  def freeVariables():Set[Var]

  def ??(thenBranch:ArithExpr):IfThenElseBuilder = {
    IfThenElseBuilder(this, thenBranch)
  }
}
object BoolExpr {
  case object True extends BoolExpr {
    override def digest = 1

    override def simplifyInnerArithExpr = this

    override def visit(f: ArithExpr => Unit) = ()

    override def visitAndRebuild(f: ArithExpr => ArithExpr) = this

    override def freeVariables() = Set()
  }
  case object False extends BoolExpr {
    override def digest = 0

    override def simplifyInnerArithExpr = this

    override def visit(f: ArithExpr => Unit) = ()

    override def visitAndRebuild(f: ArithExpr => ArithExpr) = this

    override def freeVariables() = Set()

  }
  case class ArithPredicate private(lhs:ArithExpr, rhs:ArithExpr, op:Operator) extends BoolExpr {
    val digest: Int = 0x7c6736c0 ^ lhs.digest() ^ rhs.digest() ^ op.hashCode()

    override def simplifyInnerArithExpr = arithPredicate(ExprSimplifier(lhs), ExprSimplifier(rhs), op)

    override def visit(f: ArithExpr => Unit) = {
      f(lhs)
      f(rhs)
    }

    override def visitAndRebuild(f: ArithExpr => ArithExpr) = arithPredicate(lhs.visitAndRebuild(f), rhs.visitAndRebuild(f), op)

    override def freeVariables() = ArithExpr.freeVariables(lhs).union(ArithExpr.freeVariables(rhs))

    def evaluate:Option[Boolean] = {
      import ArithPredicate.Operator
      this.op match {
        case Operator.== => if(this.lhs == this.rhs) Some(true) else None
        case Operator.!= => ArithPredicate(lhs, rhs, Operator.==).evaluate.map(x => !x)
        case Operator.< => ArithExpr.isSmaller(lhs, rhs)
        case Operator.> => ArithExpr.isSmaller(rhs, lhs)

        case Operator.<= => ArithPredicate(lhs, rhs, Operator.==).evaluate match {
          case None | Some(false) => ArithPredicate(lhs, rhs, Operator.<).evaluate
          case x => x
        }

        case Operator.>= => ArithPredicate (rhs, lhs, Operator.<=).evaluate
      }
    }
  }

  object ArithPredicate {
    object Operator extends Enumeration {
      type Operator = Value
      val < = Value("<")
      val > = Value(">")
      val <= = Value("<=")
      val >= = Value(">=")
      val != = Value("!=")
      val == = Value("==")

      def symbolString(op:Operator): String =  op match {
        case Operator.< => "<"
        case Operator.> => ">"
        case Operator.== => "=="
        case Operator.!= => "!="
        case Operator.>= => ">="
        case Operator.<= => "<="
      }
    }
  }

  def arithPredicate(lhs:ArithExpr, rhs:ArithExpr, op:Operator):BoolExpr = {

    op match {
      case ArithPredicate.Operator.< =>
        //If the left side is always strictly less the minimum right side, then the branch is always taken
        val diff = lhs - rhs
        if (diff.sign == Sign.Negative) { return True }
        if (ArithExpr.isSmaller(lhs, rhs).contains(true)) { return True }
        //If the left is always greater or equal to the right side, then the branch is never taken
        if (diff.sign == Sign.Positive) { return False }
      case _ =>
    }
    ArithPredicate(lhs, rhs, op)
  }
}
