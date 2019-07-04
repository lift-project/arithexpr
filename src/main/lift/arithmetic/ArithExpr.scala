package lift
package arithmetic

import java.util.concurrent.atomic.AtomicLong

import lift.arithmetic.BoolExpr.ArithPredicate
import lift.arithmetic.BoolExpr.ArithPredicate.Operator
import lift.arithmetic.NotEvaluableException._
import lift.arithmetic.NotEvaluableToIntException._
import lift.arithmetic.simplifier._

import scala.language.implicitConversions

/**
  * Class `ArithExpr` is the base class for arithmetic expression trees.
  *
  * An arithmetic expression is a collection of statements representing algebraic operations (+,-,*,/,...), constants
  * and variables. Precedence is taken care of using Scala's operator precedence.
  *
  * These expressions follow mostly natural arithmetic, with a few exceptions:
  * - Modulo is defined for all integers (like the remainder operator `%` in C)
  * - The division operator `/` performs an integer division (the fractional part is discarded)
  * - The operator `/^` is a division operator in the rational set (using ordinal arithmetic)
  */
abstract sealed class ArithExpr {

  /**
    * By default the expression is not simplified
    */
  val simplified: Boolean = false

  /**
    * Rebuild the expression with simplification enabled.
    *
    * @return The simplified expression.
    */
  def enforceSimplification: ArithExpr = {
    val `simplify?` = PerformSimplification.simplify
    PerformSimplification.simplify = true
    val ret = this.visitAndRebuild(x => x)
    PerformSimplification.simplify = `simplify?`
    ret
  }

  /* Should be overridden by any class that extends ArithExpr and is outside the arithmetic package */
  lazy val sign: Sign.Value = Sign(this)

  /**
    * Return the min or max of this arithmetic expression by setting all the variables to their min or max values.
    * Should be overridden by any class that extends ArithExpr and is outside the arithmetic package.
    */
  lazy val (min: ArithExpr, max: ArithExpr) = _minmax()

  /** This method should only be used internally or in special cases where we want to customise the behaviour
    * based on the variables
    */
  private def _minmax(): (ArithExpr, ArithExpr) =
    try {
      this match {
        case AbsFunction(expr) =>
          (ArithExpr.min(abs(expr.min), abs(expr.max)),
            ArithExpr.max(abs(expr.min), abs(expr.max)))
        case PosInf => (PosInf, PosInf)
        case NegInf => (NegInf, NegInf)
        case c: CeilingFunction => (ceil(c.ae.min), ceil(c.ae.max))
        case f: FloorFunction => (floor(f.ae.min), floor(f.ae.max))
        case c: Cst => (c, c)
        case Prod(factors) =>
          this.sign match {
            case Sign.Positive => (factors.map(abs(_).min).reduce[ArithExpr](_ * _), factors.map(abs(_).max).reduce[ArithExpr](_ * _))
            case Sign.Negative => (factors.map(abs(_).max).reduce[ArithExpr](_ * _) * -1, factors.map(abs(_).min).reduce[ArithExpr](_ * _) * -1)
            case Sign.Unknown => (?, ?) // impossible to determine the min and max
          }
        case Sum(terms) =>
          (terms.map(_.min).reduce[ArithExpr](_ + _), terms.map(_.max).reduce[ArithExpr](_ + _))
        case IntDiv(numer, denom) =>
          this.sign match {
            case Sign.Positive => (
              if (denom.max != Cst(0)) ExprSimplifier(numer.min / denom.max) else PosInf,
              if (denom.min != Cst(0)) ExprSimplifier(numer.max / denom.min) else PosInf)
            case Sign.Negative => (
              if (denom.min != Cst(0)) ExprSimplifier(numer.max / denom.min) else NegInf,
              if (denom.max != Cst(0)) ExprSimplifier(numer.min / denom.max) else NegInf)
            case Sign.Unknown => (?, ?) // impossible to determine the min and max
          }
        case ite: IfThenElse =>
          (ArithExpr.Math.Min(ite.t.min, ite.e.min), ArithExpr.Math.Max(ite.t.max, ite.e.max))
        case l: Log =>
          assert(l.x.sign == Sign.Positive)
          (l.x - 1).sign match {
            case Sign.Positive => (Log(l.b.max, l.x.min), Log(l.b.min, l.x.max))
            case Sign.Negative => (Log(l.b.min, l.x.max), Log(l.b.max, l.x.min))
            case _ => (?, ?) // impossible to determine the min and max
          }
        case Mod(dividend, divisor) =>
          (dividend.sign, divisor.sign) match {
            case (Sign.Positive, Sign.Positive) => (0, divisor.max - 1)
            case (Sign.Positive, Sign.Negative) => (0, (0 - divisor.max) - 1)
            case (Sign.Negative, Sign.Positive) => (0 - (divisor.max - 1), 0)
            case (Sign.Negative, Sign.Negative) => (0 - ((0 - divisor).max - 1), 0)
            case _ => (?, ?) // impossible to determine the min and max
          }
        case Pow(b, e) =>
          (b.sign, e.sign) match {
            case (Sign.Positive, Sign.Positive) => (b.min pow e.min, b.max pow e.max)
            case (Sign.Positive, Sign.Negative) => (b.min pow e.min, b.max pow e.max)
            case (Sign.Negative, Sign.Positive) => (b.max pow e.min, b.min pow e.max)
            case (Sign.Positive, _) => (?, ?) // could be anything
            case (Sign.Negative, _) => (?, ?) // could be anything
            case (_, _) => (?, ?) // unknown
          }
        case v: Var => (v.range.min.min: ArithExpr, v.range.max.max: ArithExpr)
        case ? => (?, ?)
        case _ => (?, ?)
      }
    } catch {
      case NotEvaluableException() => (?, ?)
    }

  lazy val eval: Int = evalInt

  /**
    * Evaluates an arithmetic expression.
    *
    * @return The Int value of the expression.
    * @throws NotEvaluableException      if the expression cannot be fully evaluated.
    * @throws NotEvaluableToIntException if the expression evaluated to a value larger than scala.Int.MaxValue
    */
  lazy val evalInt: Int = {
    val value = evalLong
    if (value > scala.Int.MaxValue) {
      throw NotEvaluableToInt
    }
    value.toInt
  }

  /**
    * Evaluates an arithmetic expression.
    *
    * @return The Long value of the expression.
    * @throws NotEvaluableException if the expression cannot be fully evaluated.
    */
  lazy val evalLong: Long = {
    // Evaluating is quite expensive, traverse the tree to check assess evaluability
    if (!isEvaluable)
      throw NotEvaluable
    val dblResult = ArithExpr.evalDouble(this)
    if (dblResult.isWhole())
      dblResult.toLong
    else throw NotEvaluable
  }

  lazy val evalDouble: Double = ArithExpr.evalDouble(this)

  lazy val isEvaluable: Boolean = {
    !ArithExpr.visitUntil(this, x => {
      x == PosInf || x == NegInf || x == ? ||
        x.isInstanceOf[ArithExprFunction] || x.isInstanceOf[Var] || x.isInstanceOf[IfThenElse]
    })
  }

  lazy val atMax: ArithExpr = {
    val vars = varList.filter(_.range.max != ?)
    val exprFunctions = ArithExprFunction.getArithExprFuns(this).filter(_.range.max != ?)
    val maxLens = vars.map(_.range.max) ++ exprFunctions.map(_.range.max)
    ArithExpr.substitute(this, (vars ++ exprFunctions, maxLens).zipped.toMap)
  }

  lazy val atMin: ArithExpr = {
    val vars = varList.filter(_.range.min != ?)
    val exprFunctions = ArithExprFunction.getArithExprFuns(this).filter(_.range.min != ?)
    val maxLens = vars.map(_.range.min) ++ exprFunctions.map(_.range.min)
    ArithExpr.substitute(this, (vars ++ exprFunctions, maxLens).zipped.toMap)
  }

  lazy val varList: List[Var] = ArithExpr.collectVars(this)

  def visitAndRebuild(f: ArithExpr => ArithExpr): ArithExpr

  /**
    * Fast Equality operator.
    * The function first compares the seeds, then the digests. If they are equal, the trees are compared using the
    * full equality operator.
    *
    * @param that Another expression.
    * @return True if the two expressions are equal, false otherwise.
    * @note This operator works only for simplified expressions.
    */
  def ==(that: ArithExpr): Boolean = {
    (this, that) match {
        //This library makes extensive use of construction-time computation for the various ArithExpr object - often coupled
        //with lazy vals. It sometimes happen that, while evaluating this construction-time values, bit's of unitialised
        //arithmetic expressions are compared. This hack guards against such cases.
      case (null, _) => return false
      case (_, null) => return false
      case _ =>
    }

    if (this.HashSeed() == that.HashSeed() && this.digest() == that.digest())
      this === that
    else false
  }

  def !==(that: ArithExpr): Boolean = ! == (that)

  /**
    * True equality operator. Compare each operands.
    *
    * @param that Another expression.
    * @return True iif the two expressions are equal.
    * @note This operator works only for simplified expressions.
    */
  def ===(that: ArithExpr): Boolean = (this, that) match {
    case (Cst(x), Cst(y)) => x == y
    case (IntDiv(x1, y1), IntDiv(x2, y2)) => x1 == x2 && y1 == y2
    case (Pow(x1, y1), Pow(x2, y2)) => x1 == x2 && y1 == y2
    case (Log(x1, y1), Log(x2, y2)) => x1 == x2 && y1 == y2
    case (Mod(x1, y1), Mod(x2, y2)) => x1 == x2 && y1 == y2
    case (FloorFunction(a), FloorFunction(x)) => a == x
    case (CeilingFunction(x), CeilingFunction(y)) => x == y
    case (Sum(a), Sum(b)) => a.length == b.length && (a zip b).forall(x => x._1 == x._2)
    case (Prod(a), Prod(b)) => a.length == b.length && (a zip b).forall(x => x._1 == x._2)
    case (IfThenElse(test1, t1, e1), IfThenElse(test2, t2, e2)) =>
      test1 == test2 && t1 == t2 && e1 == e2
    case (lu1: Lookup, lu2: Lookup) => lu1.table == lu2.table && lu1.index == lu2.index
    case (f1: ArithExprFunction, f2: ArithExprFunction) => f1.name == f2.name
    case (nv1: NamedVar, nv2: NamedVar) => nv1.name == nv2.name
    case (v1: Var, v2: Var) => v1.id == v2.id
    case (AbsFunction(x), AbsFunction(y)) => x == y
    case (SteppedCase(v1, cases1), SteppedCase(v2, cases2)) => v1.name == v2.name && cases1 == cases2
    case _ =>
//      System.err.println(s"$this and $that are not equal")
      false
  }

  def !===(that: ArithExpr): Boolean = ! ===(that)

  def pow(that: ArithExpr): ArithExpr with SimplifiedExpr = SimplifyPow(this, that)

  /**
    * Multiplication operator.
    *
    * @param that Right-hand side.
    * @return An expression representing the product (not necessarily a Prod object).
    */
  def *(that: ArithExpr): ArithExpr with SimplifiedExpr = SimplifyProd(this, that)

  /**
    * Addition operator.
    *
    * @param that Right-hand side.
    * @return An expression representing the sum (not necessarily a Sum object).
    */
  def +(that: ArithExpr): ArithExpr with SimplifiedExpr = SimplifySum(this, that)

  /**
    * Division operator in Natural set (ie int div like Scala): `1/2=0`.
    *
    * @param that Right-hand side (divisor).
    * @return An IntDiv object wrapping the operands.
    * @throws ArithmeticException if the right-hand-side is zero.
    */
  def /(that: ArithExpr): ArithExpr with SimplifiedExpr = SimplifyIntDiv(this, that)

  /**
    * Ordinal division operator.
    * This prevents integer arithmetic simplification through exponentiation.
    *
    * @param that Right-hand side (divisor).
    * @return The expression multiplied by the divisor exponent -1.
    */
  def /^(that: ArithExpr): ArithExpr with SimplifiedExpr = SimplifyProd(this, SimplifyPow(that, -1))

  /**
    * Transform subtraction into sum of product with -1
    *
    * @param that Right-hand side of the division
    * @return A Sum object
    */
  def -(that: ArithExpr): ArithExpr with SimplifiedExpr = this + (that * -1)

  /**
    * The % operator yields the remainder from the division of the first expression by the second.
    *
    * @param that The right-hand side (divisor)
    * @return A Mod expression
    * @throws ArithmeticException if the right-hand-side is zero.
    * @note This operation is defined for negative number since it computes the remainder of the algebraic quotient
    *       without fractional part times the divisor, ie (a/b)*b + a%b is equal to a.
    */
  def %(that: ArithExpr): ArithExpr with SimplifiedExpr = SimplifyMod(this, that)

  /**
    * +    * XOR Operator, C style
    *
    * @param that Right-hand side.
    * @return an expression representing the XOR of the two values
    */
  def ^(that: ArithExpr): ArithExpr with SimplifiedExpr = BitwiseXOR(this, that)

  /**
    * bitwise AND Operator, C style
    *
    * @param that Right-hand side.
    * @return an expression representing the bitwise AND of the two values
    */
  def &(that: ArithExpr): ArithExpr with SimplifiedExpr = BitwiseAND(this, that)

  /**
    * bitshift, left, C style
    *
    * @param that Right-hand side.
    * @return an expresison representing the left shift of the value by the right hand value
    */
  def <<(that: ArithExpr): ArithExpr with SimplifiedExpr = LShift(this, that)

  /**
    * Lower than comparison operator.
    *
    * @param that Right-hand side of the comparison
    * @return A Predicate object
    */
  def lt(that: ArithExpr) = BoolExpr.arithPredicate(this, that, BoolExpr.ArithPredicate.Operator.<)

  /**
    * Greater than comparison operator.
    *
    * @param that Right-hand side of the comparison
    * @return A Predicate object
    */
  def gt(that: ArithExpr) = BoolExpr.arithPredicate(this, that, BoolExpr.ArithPredicate.Operator.>)

  /**
    * Lower-or-equal comparison operator.
    *
    * @param that Right-hand side of the comparison
    * @return A Predicate object
    */
  def le(that: ArithExpr) = BoolExpr.arithPredicate(this, that, BoolExpr.ArithPredicate.Operator.<=)

  /**
    * Greater-or-equal comparison operator.
    *
    * @param that Right-hand side of the comparison
    * @return A Predicate object
    */
  def ge(that: ArithExpr) = BoolExpr.arithPredicate(this, that, BoolExpr.ArithPredicate.Operator.>=)

  /**
    * Equality comparison operator.
    *
    * @note Silently overrides the reference comparison operator `AnyRef.eq`
    * @param that Right-hand side of the comparison
    * @return A Predicate object
    */
  def eq(that: ArithExpr) = BoolExpr.arithPredicate(this, that, BoolExpr.ArithPredicate.Operator.==)

  /**
    * Inequality comparison operator.
    *
    * @note Silently overrides the reference comparison operator `AnyRef.ne`
    * @param that Right-hand side of the comparison
    * @return A Predicate object
    */
  def ne(that: ArithExpr) = BoolExpr.arithPredicate(this, that, BoolExpr.ArithPredicate.Operator.!=)

  /**
    * The hash function creates a 32 bit digest of the expression. Each node type has a unique salt and combines
    * the hashes of the subexpressions using a commutative and associative operator (most likely XOR).
    *
    * The probability of a collision is already fairly low, but in order to guarantee equality one should call
    * visit with a hash comparison function on the sub-tree to guarantee that each node matches. The probability
    * of a collision is then the probability of a collision of a leaf node, which is zero for constant nodes and zero
    * for the first 2,147,483,647 variable instances.
    *
    * @return A 32 bit digest of the expression.
    */
  def digest(): Int

  override def hashCode: Int = digest()

  def HashSeed(): Int
}

object ArithExpr {

  implicit def intToCst(i: Int): ArithExpr with SimplifiedExpr = Cst(i)

  implicit def longToCst(i: Long): ArithExpr with SimplifiedExpr = Cst(i)

  implicit def simplifyImplicitly(ae: ArithExpr): ArithExpr with SimplifiedExpr = ExprSimplifier(ae)
  implicit def simplifyImplicitly(aes: Seq[ArithExpr]): Seq[ArithExpr with SimplifiedExpr] = ExprSimplifier(aes)
  implicit def simplifyImplicitly(aes: List[ArithExpr]): List[ArithExpr with SimplifiedExpr] = ExprSimplifier(aes)

  val isCanonicallySorted: (ArithExpr, ArithExpr) => Boolean = (x: ArithExpr, y: ArithExpr) => (x, y) match {
    case (Cst(a), Cst(b)) => a < b
    case (_: Cst, _) => true // constants first
    case (_, _: Cst) => false
    case (x:NamedVar, y:NamedVar) => x.name.compareTo(y.name) <= 0
    case (x: Var, y: Var) => x.id < y.id // order variables based on id
    case (_: Var, _) => true // variables always after constants second
    case (_, _: Var) => false
    case (Prod(factors1), Prod(factors2)) => factors1.zip(factors2).map(x => isCanonicallySorted(x._1, x._2)).foldLeft(false)(_ || _)
    case _ => x.HashSeed() < y.HashSeed() || (x.HashSeed() == y.HashSeed() && x.digest() < y.digest())
  }

  def ifThenElse(p:BoolExpr, `then`:ArithExpr, `else`:ArithExpr):ArithExpr = SimplifyIfThenElse(p, `then`, `else`)

  def gcd(a: ArithExpr, b: ArithExpr): ArithExpr = ComputeGCD(a, b)

  def max(e1: ArithExpr, e2: ArithExpr): ArithExpr = minmax(e1, e2)._2

  def min(e1: ArithExpr, e2: ArithExpr): ArithExpr = minmax(e1, e2)._1

  def minmax(e1: ArithExpr, e2: ArithExpr): (ArithExpr, ArithExpr) = {
    e1 - e2 match {
      case Cst(c) if c < 0 => (e1, e2) /* e1 is smaller than e2 */
      case Cst(_) => (e2, e1) /* e2 is smaller than e1*/
      case _ =>
        (e1, e2) match {
          case (v: Var, c: Cst) => minmax(v, c)
          case (c: Cst, v: Var) => minmax(v, c).swap

          case (Prod(factors), c: Cst) => minmax(e1, factors, c)
          case (c: Cst, Prod(factors)) => minmax(e2, factors, c).swap

          case _ => throw NotEvaluable
        }
    }
  }

  def minmax(v: Var, c: Cst): (ArithExpr, ArithExpr) = {
    val m1 = v.range.min match {
      case Cst(min) => if (min >= c.c) Some((c, v)) else None
      case `?` => throw NotEvaluable
      case _ => throw new NotImplementedError()
    }

    if (m1.isDefined) return m1.get

    val m2 = v.range.max match {
      case Cst(max) => if (max <= c.c) Some((v, c)) else None
      case _ => throw new NotImplementedError()
    }

    if (m2.isDefined) return m2.get

    throw NotEvaluable
  }

  def minmax(p: ArithExpr, pFactors: List[ArithExpr], c: Cst): (ArithExpr, ArithExpr) = {
    try {
      val lb = lowerBound(pFactors)
      if (lb.isDefined && lb.get >= c.c) return (c, p)

      val ub = upperBound(pFactors)
      if (ub.isDefined && ub.get <= c.c) return (p, c)
    } catch {
      case _: IllegalArgumentException =>
    }

    throw NotEvaluable
  }

  private def upperBound(factors: List[ArithExpr]): Option[Long] = {
    Some(SimplifyProd(factors.map({
      case v: Var => v.range.max match {
        case max: Cst => max
        case _ => return None
      }
      case c: Cst => c
      case _ => throw new IllegalArgumentException("upperBound expects a Var or a Cst")
    })).eval)
  }

  private def lowerBound(factors: List[ArithExpr]): Option[Long] = {
    Some(SimplifyProd(factors.map({
      case v: Var => v.range.min match {
        case min: Cst => min
        case _ => return None
      }
      case c: Cst => c
      case _ => throw new IllegalArgumentException("lowerBound expects a Var or a Cst")
    })).eval)
  }


  def contains(expr: ArithExpr, elem: ArithExpr): Boolean = {
    visit(expr, e => if (e == elem) return true)
    false
  }

  /**
    * Find if an expression is possibly a multiple of another.
    *
    * @param expr The expression.
    * @param that A possible multiple.
    * @return True if `that` is a multiple of `expr`, false otherwise
    */
  def multipleOf(expr: ArithExpr, that: ArithExpr): Boolean = (ExprSimplifier(expr), that) match {

    // Compare two products, look for inclusion of common denominator
    case (Prod(terms), Prod(otherTerms)) => terms.count(isDivision) == otherTerms.count(isDivision) && otherTerms.map({
      case pow: Pow => terms.exists(multipleOf(_, pow))
      case x => terms.contains(x)
    }).reduce(_ && _)

    // A constant is a multiple of a product if it is a multiple of its constant factor
    case (Prod(terms), Cst(c)) =>
      val cst = terms.find(_.isInstanceOf[Cst])
      cst.isDefined && cst.get.asInstanceOf[Cst].c % c == 0

    // If it is something else, it is a multiple if it is included in the list of factors and the product does not
    // contain a division
    case (Prod(terms), _) => !terms.exists(isDivision) && terms.contains(that)

    // Check multiple of constants
    case (Cst(c1), Cst(c2)) => c1 % c2 == 0

    // Look for common denominator in fractions
    case (IntDiv(n1, d1), IntDiv(n2, d2)) => multipleOf(d2, d1) && multipleOf(n1, n2)

    // Look for the denominator for two inverses
    case (Pow(b1, Cst(-1)), Pow(b2, Cst(-1))) => multipleOf(b2, b1)

    // Finally, the two expressions are multiple of each other if they are the same
    case (x, y) => x == y
  }

  private[arithmetic] def hasDivision(factors: List[ArithExpr]): Boolean = {
    factors.exists(isDivision)
  }

  private[arithmetic] def isDivision: (ArithExpr) => Boolean = {
    case Pow(_, Cst(x)) if x < 0 => true
    case _ => false
  }


  def collectVars(ae: ArithExpr): List[Var] = {
    val vars = new scala.collection.mutable.ListBuffer[Var]()
    ArithExpr.visit(ae, {
      case v: Var =>
        vars += v
        vars ++= collectVars(v.range.max)
        vars ++= collectVars(v.range.min)
      case _ =>
    }
    )
    vars.distinct.toList
  }

  def mightBeNegative(expr: ArithExpr): Boolean = {
    expr.sign != Sign.Positive
  }

  /**
    * Return true if ae1 is definitively smaller than ae2.
    * Return false if this cannot be proven (this does not mean that ae1 is always larger than ae2)
    */
  def isSmaller(ae1: ArithExpr, ae2: ArithExpr): Option[Boolean] = {

    // 1) if ae1 and ae2 constants, return True or False
    // 2) collect all the variables that appears only in ae1 or only in ae2
    // 3) if no unique var, then return : don't know
    // 4) call isSmaller (max(ae1),min(ae2)) by forcing min and max to only set the unique vars (in other word the min or max of all the other var should be the var itself (and not the min or max of its range))
    // this can be achieved probably by rewriting the expression using a special var which wraps the original var, and when the call returns we can unwrap them, this is needed to ensure the min or max of these var is the var itself

    try {
      // we check to see if the difference can be evaluated
      val diff = ae2 - ae1
      if (diff.isEvaluable)
        return Some(diff.evalDouble > 0)
    } catch {
      case NotEvaluableException() =>
    }

    try {
      return Some(ae1.max.evalLong < ae2.min.evalLong)
    } catch {
      case NotEvaluableException() =>
    }

    // TODO: Find a more generic solution for these cases
    (ae1, ae2) match {
      // a * v /^ b < v (true if a < b)
      case (Prod(Cst(c1) :: (v1: Var) :: Pow(Cst(c2), Cst(-1)) :: Nil), v2: Var) if v1 == v2 && c1 < c2 =>
        return Some(true)
      // v /^ a < v (true if a > 1)
      case (Prod((v1: Var) :: Pow(Cst(c), Cst(-1)) :: Nil), v2: Var) if v1 == v2 && c > 1 =>
        return Some(true)
      // a < b (true if a.max < b)
      // Adding 1 seems to be a simple heuristic: if range is RangeAdd, then range.max
      // has -1 in it. By adding 1, we make the max simpler to compare, and if a + 1 < b,
      // then a < b, so it is safe
      case (v1: Var, v2: Var) if isSmaller(v1.range.max + 1, v2).getOrElse(false) =>
        return Some(true)
      // Abs(a + x) < n true if (a + x) < n and -1(a + x) < n
      case (AbsFunction(Sum((a: Cst) :: (x: Var) :: Nil)), n: Var) if
      isSmaller(SimplifySum(a :: x.range.max :: Nil), n).getOrElse(false) &&
        isSmaller(SimplifyProd(Cst(-1) :: SimplifySum(a :: x.range.min :: Nil) :: Nil), n).getOrElse(false) =>
        return Some(true)
      case (Mod((_: ArithExpr), (v1: Var)), (v2: Var)) if v1 == v2 =>
        return Some(true)
      // z < x/y and y > 0  iff  y * z < x
      case (_, Prod(p)) if p.exists(ArithExpr.isInverse) =>
        // Fetch the terms of the form Pow(…, -1), inverse and isolate them
        val (inverses, rem) = p.partition(ArithExpr.isInverse) match {
          case (inv, r) => (
            SimplifyProd(
              inv.map({
                case Pow(x, Cst(-1)) => x
                case _ => throw new IllegalArgumentException() // Cannot happen at this point
              })),
            SimplifyProd(r)
          )
        }
        val result = inverses.sign match {
          case Sign.Positive => isSmaller(ae1 * inverses, rem)
          case Sign.Negative => isSmaller(rem, ae1 * inverses)
          case _ => None
        }
        if (result.isDefined) return result
      // z < c*(x + y)  iff  z/c < x + y  Especially useful when c = 1 /^ something
      case (_, Sum(List(Prod(x), Prod(y)))) =>
        val (fact, sum) = factorize(x, y)
        // We have to check that a factorization has actually been performed
        if (!(fact == Cst(1))) {
          val result = fact.sign match {
            case Sign.Positive => isSmaller(ae1 /^ fact, sum)
            case Sign.Negative => isSmaller(sum, ae1 /^ fact)
            case _ => None
          }
          if (result.isDefined)
            return result
        }
      //                         Do not try this if `max` and `min` do not tell anything
      case (IntDiv(a, b), c) if (a, b, c) != (a.max, b.min, c.min) &&
        isSmaller(a.max / b.min, c.min).getOrElse(false) =>
        return Some(true)
      case _ =>
    }

    // if we see an opaque var or unknown, we cannot say anything
    if (ae1.isInstanceOf[OpaqueVar] | ae2.isInstanceOf[OpaqueVar] | ae1 == ? | ae2 == ?)
      return None

    //  handling of infinite values
    (ae1, ae2) match {
      case (PosInf, PosInf) => return None
      case (NegInf, NegInf) => return None
      case (PosInf, NegInf) => return Some(false)
      case (NegInf, PosInf) => return Some(true)
      case (PosInf, _) if ae2.isEvaluable => return Some(false)
      case (NegInf, _) if ae2.isEvaluable => return Some(true)
      case (_, NegInf) if ae1.isEvaluable => return Some(false)
      case (_, PosInf) if ae1.isEvaluable => return Some(true)

      case _ =>
    }

    // See TestExpr.numValsNotSimplifying2 and RangeAdd.numValues
    val fun1 = ArithExprFunction.getArithExprFuns(ae1)
    val fun2 = ArithExprFunction.getArithExprFuns(ae2)
    val union = fun1 ++ fun2

    if (union.nonEmpty) {
      val replacements = union.map(f => Var(f.name, f.range))
      val replacementsMap = (union, replacements).zipped.toMap[ArithExpr, ArithExpr]

      // Disable simplification before rebuilding to save time
      // This is allowed because obscuring vars (replacing them with opaques) does not add new information,
      // so no new simplification will be possible.
      val originalSimplificationFlag = PerformSimplification.simplify
      PerformSimplification.simplify = false
      val substitute1 = ArithExpr.substitute(ae1, replacementsMap)
      val substitute2 = ArithExpr.substitute(ae2, replacementsMap)
      PerformSimplification.simplify = originalSimplificationFlag

      //If substituting had no effect, give up now
      return if(ae1 == substitute1 && ae2 == substitute2) {
        None
      } else {
        isSmaller(substitute1, substitute2)
      }
    }

    val ae1Vars = collectVars(ae1).filter(_ match { case _: OpaqueVar => false case _ => true }).toSet
    val ae2Vars = collectVars(ae2).filter(_ match { case _: OpaqueVar => false case _ => true }).toSet
    val commonVars = ae1Vars & ae2Vars

    val varsOnlyInae1 = ae1Vars -- commonVars
    val varsOnlyInae2 = ae2Vars -- commonVars
    val varsOnlyInae1orae2 = varsOnlyInae1 ++ varsOnlyInae2

    if (varsOnlyInae1orae2.isEmpty)
      return None

    val replacements = commonVars.map(v => (v, new OpaqueVar(v))).toMap
    // Disable simplification before rebuilding to save time
    // This is allowed because obscuring vars (replacing them with opaques) does not add new information,
    // so no new simplification will be possible.
    val originalSimplificationFlag = PerformSimplification.simplify
    PerformSimplification.simplify = false
    val ae1WithFixedVars = ArithExpr.substitute(ae1, replacements.toMap)
    val ae2WithFixedVars = ArithExpr.substitute(ae2, replacements.toMap)
    PerformSimplification.simplify = originalSimplificationFlag

    try {
      val ae1WithFixedVarsMax = ae1WithFixedVars.max
      val ae2WithFixedVarsMin = ae2WithFixedVars.min
      isSmaller(ae1WithFixedVarsMax, ae2WithFixedVarsMin)
    } catch {
      case NotEvaluableException() => None
    }
  }

  /**
    * Warning, this function does not visit the range inside the var (maybe we wants this?)
    */
  def visit(e: ArithExpr, f: (ArithExpr) => Unit): Unit = {
    f(e)
    e match {
      case Pow(base, exp) =>
        visit(base, f)
        visit(exp, f)
      case IntDiv(n, d) =>
        visit(n, f)
        visit(d, f)
      case Mod(dividend, divisor) =>
        visit(dividend, f)
        visit(divisor, f)
      case Log(b, x) =>
        visit(b, f)
        visit(x, f)
      case FloorFunction(expr) => visit(expr, f)
      case CeilingFunction(expr) => visit(expr, f)
      case Sum(terms) => terms.foreach(t => visit(t, f))
      case Prod(terms) => terms.foreach(t => visit(t, f))
      case IfThenElse(test, thenE, elseE) =>
        test.visit(f)
        visit(thenE, f)
        visit(elseE, f)
      case lu: Lookup =>
        visit(lu.index, f)
        lu.table.foreach(t => visit(t, f))
      case BigSum(binder, body) =>
        visit(binder, f)
        visit(body, f)
      case SteppedCase(v, cases) =>
        visit(v, f)
        cases.foreach(visit(_, f))
      case Var(_, _) | Cst(_) | ArithExprFunction(_, _) =>
      case x if x.getClass == ?.getClass =>
      case PosInf | NegInf =>
      case AbsFunction(expr) => visit(expr, f)
    }
  }

  def visitUntil(e: ArithExpr, f: (ArithExpr) => Boolean): Boolean = {
    if (f(e)) true
    else {
      e match {
        case Pow(base, exp) =>
          visitUntil(base, f) || visitUntil(exp, f)
        case IntDiv(n, d) =>
          visitUntil(n, f) || visitUntil(d, f)
        case Mod(dividend, divisor) =>
          visitUntil(dividend, f) || visitUntil(divisor, f)
        case Log(b, x) =>
          visitUntil(b, f) || visitUntil(x, f)
        case FloorFunction(expr) => visitUntil(expr, f)
        case CeilingFunction(expr) => visitUntil(expr, f)
        case Sum(terms) =>
          terms.foreach(t => if (visitUntil(t, f)) return true)
          false
        case Prod(terms) =>
          terms.foreach(t => if (visitUntil(t, f)) return true)
          false
        case gc: Lookup => visitUntil(gc.index, f)
        case BigSum(variable, body) =>
          visitUntil(variable, f) || visitUntil(body, f)
        case SteppedCase(v, cases) =>
          visitUntil(v, f) || visitUntilGroup(cases, f)
        case Var(_, _) | Cst(_) | IfThenElse(_, _, _) | ArithExprFunction(_, _) => false
        case x if x.getClass == ?.getClass => false
        case PosInf | NegInf => false
        case AbsFunction(expr) => visitUntil(expr, f)
      }
    }
  }

  private def visitUntilGroup(items:Iterable[ArithExpr], f:ArithExpr => Boolean):Boolean = {
    items.foreach(t => if(visitUntil(t, f)) return true)
    false
  }

  /***
    * Returns the set of all variables in the expression which are not locally scoped.
    * @param rootExpr
    * @return
    */
  def freeVariables(rootExpr:ArithExpr):Set[Var] = {
    //If we had a reverse-visit...I would not have to re-write a pattern matching cascade...
    //...but we don't...so sad :(
    def fv(expr:ArithExpr):Set[Var] = {
      expr match {
        case Pow(base, exp) => fv(base) ++ fv(exp)
        case IntDiv(numer, denom) => fv(numer) ++ fv(denom)
        case Mod(dividend, divisor) => fv(dividend) ++ fv(divisor)
        case Log(b, x) => fv(b) ++ fv(x)
        case FloorFunction(expr) => fv(expr)
        case CeilingFunction(expr) => fv(expr)
        case Sum(terms) => terms.map(fv).foldLeft(Set[Var]())(_ ++ _)
        case Prod(terms) => terms.map(fv).foldLeft(Set[Var]())(_ ++ _)
        case IfThenElse(test, thenE, elseE) =>
          test.freeVariables ++ fv(thenE) ++ fv(elseE)
        case lu: Lookup => fv(lu.index) ++ lu.table.map(fv).foldLeft(Set[Var]())(_ ++ _)
        case BigSum(binder, body) => fv(body) - binder
        case SteppedCase(v, cases) => cases.map(fv).foldLeft(Set[Var]())(_ ++ _) + v
        case v:Var  => Set(v)
        case Cst(_) => Set()
        case fun:ArithExprFunction => fun.freeVariables
        case x if x.getClass == ?.getClass => Set()
        case PosInf | NegInf => Set()
        case AbsFunction(expr) => fv(expr)
      }
    }

    fv(rootExpr)
  }

  def substitute(e: ArithExpr, substitutions: scala.collection.Map[ArithExpr, ArithExpr]): ArithExpr =
    e.visitAndRebuild(expr =>
      if (substitutions.isDefinedAt(expr))
        substitutions(expr)
      else
        expr
    )

  /**
    * Substitutes y * Pow(x, -1) operator with y / x. Added to get around
    * comparison issues. Both will print to the same C code.
    *
    * @return
    */
  def substituteDiv(e: ArithExpr): ArithExpr =
    e.visitAndRebuild({
      case Prod(factors) =>
        factors.foldLeft(Cst(1): ArithExpr)((exprSoFar, newTerm) =>
          newTerm match {
            case Pow(b, Cst(-1)) => exprSoFar / b
            case _ => exprSoFar * newTerm
          })
      case x => x
    })

  private def evalDouble(e: ArithExpr): Double = e match {
    case Cst(c) => c

    case IntDiv(n, d) => scala.math.floor(evalDouble(n) / evalDouble(d))


    case Pow(base, exp) => scala.math.pow(evalDouble(base), evalDouble(exp))
    case Log(b, x) => scala.math.log(evalDouble(x)) / scala.math.log(evalDouble(b))

    case Mod(dividend, divisor) => dividend.eval % divisor.eval

    case Sum(terms) => terms.foldLeft(0.0)((result, expr) => result + evalDouble(expr))
    case Prod(terms) => terms.foldLeft(1.0)((result, expr) => result * evalDouble(expr))

    case FloorFunction(expr) => scala.math.floor(evalDouble(expr))
    case CeilingFunction(expr) => scala.math.ceil(evalDouble(expr))

    case AbsFunction(expr) => scala.math.abs(evalDouble(expr))

    case IfThenElse(_, _, _) => throw NotEvaluable

    case BigSum(idxVariable, body) =>
      val lowerBound = evalDouble(idxVariable.rangeAdd.start).toInt
      val upperBound = evalDouble(idxVariable.rangeAdd.stop).toInt

      def mkBody = (idxValue:ArithExpr) => ArithExpr.substitute(body, Map(idxVariable -> idxValue))

      (lowerBound until upperBound).map(varValue => evalDouble(mkBody(varValue))).sum

    case steppedCase:SteppedCase => evalDouble(steppedCase.intoIfChain())

    case `?` | NegInf | PosInf | _: Var | _: ArithExprFunction | _: SimplifiedExpr => throw NotEvaluable
  }


  def toInt(e: ArithExpr): Int = ExprSimplifier(e) match {
    case Cst(i) => i.asInstanceOf[Int]
    case _ => throw NotEvaluable
  }


  def asCst(e: ArithExpr): Cst = ExprSimplifier(e) match {
    case c: Cst => c
    case _ => throw new IllegalArgumentException
  }

  private def isInverse(e: ArithExpr): Boolean = ExprSimplifier(e) match {
    case Pow(_, Cst(-1)) => true
    case _ => false
  }

  // factorize(e1, e2) returns a pair `(c, s)` such as
  //     `e1 + e2 = c * (e1' + e2')`
  // and `s = e1' + e2'`
  // TODO: refactor to 1. return lists of factors/terms and 2. use factorisation in Sum.asProd
  def factorize(e1factors: List[ArithExpr], e2factors: List[ArithExpr]): (ArithExpr, ArithExpr) = {
    def find[T](l: List[T], p: T => Boolean): Option[(T, List[T])] = {
      l match {
        case Nil => None
        case x :: xs =>
          if (p(x))
            Some((x, xs))
          else
            find(xs, p) match {
              case None => None
              case Some((y, ys)) => Some((y, x :: ys))
            }
      }
    }

    val init = (List(): List[ArithExpr], List(): List[ArithExpr], e2factors)
    val (common, newE2, newE1) = e1factors.foldLeft(init)({
      case ((com, unmatched, rem), e) => find(rem, (_: ArithExpr) == e) match {
        case None => (com, e :: unmatched, rem)
        case Some((x, xs)) => (x :: com, unmatched, xs)
      }
    })
    (SimplifyProd(common), SimplifySum((newE1, newE2) match {
      case (Nil, Nil) =>  throw new IllegalArgumentException(f"Could not factorize $e1factors and $e2factors")
      case (_, Nil) => List(SimplifyProd(newE1))
      case (Nil, _) => List(SimplifyProd(newE2))
      case (_, _) => List(SimplifyProd(newE1), SimplifyProd(newE2))
    }))
  }

  /**
    * Recursively converts an arithmetic expression to a Scala notation String which can be evaluated into a
    * valid ArithExpr.
    *
    * @param ae An expression to print
    * @param printNonFixedVarIds Indicates whether variables should be printed with their non-fixed IDs
    * @return Printed result
    */
  def printToScalaString(ae: ArithExpr, printNonFixedVarIds: Boolean): String = ae match {
    case Cst(v) =>                   s"Cst($v)"
    case IntDiv(numer, denom) =>     s"(${printToScalaString(numer, printNonFixedVarIds)}) / " +
                                        s"(${printToScalaString(denom, printNonFixedVarIds)})"
    case Pow(b, e) => e match {
      case Cst(-1) =>                s"Cst(1)/^(${printToScalaString(b, printNonFixedVarIds)})"
      case _ =>                      s"SimplifyPow(${printToScalaString(b, printNonFixedVarIds)}, " +
                                        s"${printToScalaString(e, printNonFixedVarIds)})"
    }
    case Log(b, x) =>                s"Log(${printToScalaString(b, printNonFixedVarIds)}, " +
                                        s"${printToScalaString(x, printNonFixedVarIds)})"
    case Prod(factors) =>
      if (factors.nonEmpty)          factors.map(printToScalaString(_, printNonFixedVarIds)).mkString(
                                        "SimplifyProd(List(", ", ", "))")
      else                           s"SimplifyProd(List())"
    case Sum(terms) =>
      if (terms.nonEmpty)            terms.map(printToScalaString(_, printNonFixedVarIds)).mkString(
                                        "SimplifySum(List(", ", ", "))")
      else                           s"SimplifySum(List())"
    case BigSum(variable, body) =>  s"SimplifyBigSum(BigSum(${printToScalaString(variable, printNonFixedVarIds)}, ${printToScalaString(body, printNonFixedVarIds)}))"
    case Mod(dividend, divisor) =>   s"SimplifyMod(${printToScalaString(dividend, printNonFixedVarIds)}, " +
                                        s"${printToScalaString(divisor, printNonFixedVarIds)})"
    case AbsFunction(e) =>           s"SimplifyAbs(${printToScalaString(e, printNonFixedVarIds)})"
    case FloorFunction(e) =>         s"SimplifyFloor(${printToScalaString(e, printNonFixedVarIds)})"
    case CeilingFunction(e) =>       s"SimplifyCeiling(${printToScalaString(e, printNonFixedVarIds)})"
    case IfThenElse(test, t, e) =>   s"SimplifyIfThenElse(${printToScalaString(test, printNonFixedVarIds)}, " +
                                        s"${printToScalaString(t, printNonFixedVarIds)}, " +
                                        s"${printToScalaString(e, printNonFixedVarIds)})"
    case ArithExprFunction(name, range) =>
                                      "ArithExprFunction(\"" + s"$name" + "\"" +
                                        s", ${Range.printToScalaString(range, printNonFixedVarIds)})"
    case BitwiseXOR(a, b) =>         s"BitwiseXOR(${printToScalaString(a, printNonFixedVarIds)}, " +
                                        s"${printToScalaString(b, printNonFixedVarIds)})"
    case BitwiseAND(a, b) =>         s"BitwiseAND(${printToScalaString(a, printNonFixedVarIds)}, " +
                                        s"${printToScalaString(b, printNonFixedVarIds)})"
    case LShift(a, b) =>             s"LShift(${printToScalaString(a, printNonFixedVarIds)}, " +
                                        s"${printToScalaString(b, printNonFixedVarIds)})"
    case v:InclusiveIndexVar =>      printVarToScalaString("InclusiveIndexVar", v, printNonFixedVarIds)
    case v:NamedVar =>      printVarToScalaString("NamedVar", v, printNonFixedVarIds)
    case v:Var =>                     printVarToScalaString("Var", v, printNonFixedVarIds)

    case e =>
      throw new NotImplementedError(
        s"Arithmetic expression $e is not supported in printing ArithExpr to Scala notation String")
  }

  private def printVarToScalaString(varTypeName:String, v:Var, printNonFixedVarIds:Boolean) = {
    varTypeName + "(\"" + s"${v.name}" + "\"" +
      s", ${Range.printToScalaString(v.range, printNonFixedVarIds)}, " +
      (if (printNonFixedVarIds) s"Some(${v.id})" else v.fixedId match {
        case Some(fixedId) => s"Some($fixedId)"
        case None => "None"}) + ")"
  }

  def printToScalaString(pred:BoolExpr, printNonFixedVarIDs:Boolean):String = pred match {
    case BoolExpr.True => "BoolExpr.True"
    case BoolExpr.False => "BoolExpr.False"
    case BoolExpr.ArithPredicate(lhs, rhs, op) =>
      s"ArithPredicate(${printToScalaString(lhs,printNonFixedVarIDs)}, " +
        s"${printToScalaString(rhs, printNonFixedVarIDs)}, " +
        s"ArithExpr.Operator.${ArithPredicate.Operator.symbolString(op)})"
  }


  /**
    * Math operations derived from the basic operations
    */
  object Math {
    /**
      * Computes the minimal value between the two argument
      *
      * @param x The first value
      * @param y The second value
      * @return The minimum between x and y
      */
    def Min(x: ArithExpr, y: ArithExpr): ArithExpr = {
      // Since Min duplicates the expression, we simplify it in place to point to the same node
      val sx = ExprSimplifier(x)
      val sy = ExprSimplifier(y)
      ifThenElse(sx le sy, sx, sy)
    }

    /**
      * Computes the maximal value between the two argument
      *
      * @param x The first value
      * @param y The second value
      * @return The maximum between x and y
      */
    def Max(x: ArithExpr, y: ArithExpr): ArithExpr = {
      // Since Max duplicates the expression, we simplify it in place to point to the same node
      val sx = ExprSimplifier(x)
      val sy = ExprSimplifier(y)
      ifThenElse(sx gt sy, sx, sy)
    }

    /**
      * Clamps a value to a given range
      *
      * @param x   The input value
      * @param min Lower bound of the range
      * @param max Upper bound of the range
      * @return The value x clamped to the interval [min,max]
      */
    def Clamp(x: ArithExpr, min: ArithExpr, max: ArithExpr) = Min(Max(x, min), max)
  }
}

trait SimplifiedExpr extends ArithExpr {
  override val simplified = true
}

/* ? represents an unknown value. */
case object ? extends ArithExpr with SimplifiedExpr {
  override val HashSeed = 0x3fac31

  override val digest: Int = HashSeed

  override lazy val sign = Sign.Unknown

  override def ==(that: ArithExpr): Boolean = that.getClass == this.getClass

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr = f(this)
}

case object PosInf extends ArithExpr with SimplifiedExpr {
  override val HashSeed = 0x4a3e87

  override val digest: Int = HashSeed

  override lazy val sign = Sign.Positive

  override def ==(that: ArithExpr): Boolean = that.getClass == this.getClass

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr = f(this)
}

case object NegInf extends ArithExpr with SimplifiedExpr {
  override val HashSeed = 0x4a3e87

  override val digest: Int = HashSeed

  override lazy val sign = Sign.Negative

  override def ==(that: ArithExpr): Boolean = that.getClass == this.getClass

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr = f(this)
}

case class Cst private[arithmetic](c: Long) extends ArithExpr with SimplifiedExpr {
  override val HashSeed: Int = java.lang.Long.hashCode(c)

  override lazy val digest: Int = java.lang.Long.hashCode(c)

  override lazy val toString: String = c.toString

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr = f(this)
}

case class IntDiv private[arithmetic](numer: ArithExpr with SimplifiedExpr, denom: ArithExpr with SimplifiedExpr)
  extends ArithExpr() {
  if (denom == Cst(0))
    throw new ArithmeticException()

  override val HashSeed = 0xf233de5a

  override lazy val digest: Int = HashSeed ^ numer.digest() ^ ~denom.digest()

  override def toString: String = s"(($numer) / ($denom))"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(numer.visitAndRebuild(f) / denom.visitAndRebuild(f))
}

object IntDiv {
  def unapply(ae: ArithExpr): Option[(ArithExpr with SimplifiedExpr, ArithExpr with SimplifiedExpr)] =
    ae match {
      case i: IntDiv => Some(i.numer, i.denom)
      case _ => None
    }
}

case class Pow private[arithmetic](b: ArithExpr with SimplifiedExpr, e: ArithExpr with SimplifiedExpr)
  extends ArithExpr {
  override val HashSeed = 0x63fcd7c2

  override lazy val digest: Int = HashSeed ^ b.digest() ^ e.digest()

  lazy val asProd: Option[List[ArithExpr with SimplifiedExpr]] = (b, e) match {
    /**  (a * b * c)^e  :  a^e * b^e * c^e  **/
    case (Prod(factors), _) => Some(factors.map(SimplifyPow(_, e)))
    /**  b^(a + c + d)  :  b^a * b^c * b^d  **/
    case (b, Sum(exps)) => Some(exps.map(SimplifyPow(b, _)))
    case (_, _) => None
  }

  override def toString: String = e match {
    case Cst(-1) => "(1/^(" + b + "))"
    case Cst(2) => s"($b * $b)"
    case _ => "pow(" + b + "," + e + ")"
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(b.visitAndRebuild(f).pow(e.visitAndRebuild(f)))
}

object Pow {
  def unapply(ae: ArithExpr): Option[(ArithExpr with SimplifiedExpr, ArithExpr with SimplifiedExpr)] = ae match {
    case p: Pow => Some(p.b, p.e)
    case _ => None
  }
}

case class Log private[arithmetic](b: ArithExpr with SimplifiedExpr, x: ArithExpr with SimplifiedExpr)
  extends ArithExpr with SimplifiedExpr {
  override val HashSeed = 0x370285bf

  override lazy val digest: Int = HashSeed ^ b.digest() ^ ~x.digest()

  override def toString: String = "log" + b + "(" + x + ")"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(Log(b.visitAndRebuild(f), x.visitAndRebuild(f)))
}

/**
  * Represent a product of two or more expressions.
  *
  * @param factors The list of factors. The list should contain at least 2 operands and should not contain other products.
  */
case class Prod private[arithmetic](factors: List[ArithExpr with SimplifiedExpr]) extends ArithExpr {
  Debug.Assert(factors.length > 1, s"Factors should have at least two terms in $toString")

  if (Debug.SanityCheck && simplified) {
    Debug.Assert(factors.view.zip(factors.tail).forall(x => ArithExpr.isCanonicallySorted(x._1, x._2)), "Factors should be sorted")
    factors.foreach(x => {
      Debug.AssertNot(x.isInstanceOf[Prod], s"Prod cannot contain a Prod in $toString")
      Debug.AssertNot(x.isInstanceOf[Sum], "Prod should not contain a Sum")
    })
  }

  override val HashSeed = 0x286be17e

  override lazy val digest: Int = factors.foldRight(HashSeed)((x, hash) => hash ^ x.digest())

  override def equals(that: Any): Boolean = that match {
    case Prod(factors2)=> factors.length == factors2.length && factors.intersect(factors2).length == factors.length
    case _ => false
  }

  override lazy val toString: String = {
    val m = if (factors.nonEmpty) factors.mkString("*") else ""
    "(" + m + ")"
  }

  def contains(e: ArithExpr): Boolean = factors.contains(e)

  /**
    * Remove a list of factors from the factors of the product and return either a Product with the remaining factors,
    * the only factors left or 1 in the case of removing all factors.
    * Removing factors does not create new optimization opportunity, therefore the resulting prod is still simplified.
    */
  def withoutFactors(list: List[ArithExpr]): ArithExpr = {
//    assert(simplified, "This function only works on simplified products")
    val rest: List[ArithExpr] = Prod.removeFactors(factors, list)
    // If there is only one left, return it
    if (rest.length == 1) rest.head
    // Otherwise create a new product, which is also simplified by construction
    else new Prod(rest)// with SimplifiedExpr
  }

  def withoutFactor(factor: ArithExpr): ArithExpr = withoutFactors(List(factor))

  lazy val cstFactor: Cst = Prod.cstFactor(factors, simplified)

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(factors.map(_.visitAndRebuild(f)).reduce(_ * _))

  // a^n * b^n : (a * b)^n
  lazy val asPowOfProd: Option[Pow] = {
    // Collect
    val prodFactorsAsPowers = Some(factors.map{
      case Pow(b, e) => Some((b, e))
      case _ => None
    })

    val firstExponent = prodFactorsAsPowers.get.head.get._2

    // Check if all product factors are powers
    if (prodFactorsAsPowers.get.forall(_.isDefined) &&
      !(firstExponent == Cst(1)) &&
      // Check if all exponents are the same
      prodFactorsAsPowers.get.forall(_.get._2 == firstExponent))
      Some(Pow(
        b = prodFactorsAsPowers.get.map(_.get._1).reduce(_ * _),
        e = firstExponent)) // Not simplifying on purpose, since it is a temporary representation
    else
      None
  }
}


object Prod {
  def unapply(ae: Any): Option[List[ArithExpr with SimplifiedExpr]] = ae match {
    case aexpr: ArithExpr => aexpr match {
      // Concrete Pow that can be represented as Prod
      case p: Pow if p.asProd.isDefined => p.asProd

      // An ArithExpr that can be represented as Pow that can be represented as Prod
      /**  (a * b * c)^e  :  a^e * b^e * c^e  **/
      case Pow(Prod(factors), e) => Some(factors.map(SimplifyPow(_, e)))

      /**  b^(a + c + d)  :  b^a * b^c * b^d  **/
      case Pow(b, Sum(exps)) => Some(exps.map(SimplifyPow(b, _)))

      // (x*a + x*b + x*c)  :  x*(a + b + c)
      case s: Sum => s.asProd match {
        case Some(productWithCommonFactor) => Some(productWithCommonFactor.factors)
        case None => None
      }
      case p: Prod => Some(p.factors)
      case _ => None
    }
    case _ => None
  }

  def removeFactors(from: List[ArithExpr], toRemove: List[ArithExpr]): List[ArithExpr] =
    from.diff(toRemove) match {
      // If we took all the elements out, return neutral (1 for product)
      case Nil => List(Cst(1))
      case x => x
    }

  def cstFactor(factors: List[ArithExpr], simplified: Boolean): Cst = {
    if (simplified) factors.find(_.isInstanceOf[Cst]).getOrElse(Cst(1)).asInstanceOf[Cst]
    else Cst(factors.filter(_.isInstanceOf[Cst]).foldLeft[Long](1)(_ * _.asInstanceOf[Cst].c))
  }

  def partitionFactorsOnCst(factors: List[ArithExpr], simplified: Boolean): (Cst, List[ArithExpr]) = {
    factors.partition(_.isInstanceOf[Cst]) match {
      case (Nil, nonCstFactors) => (Cst(1), nonCstFactors)
      case (cstFactor, nonCstFactors) => (Cst(cstFactor.foldLeft[Long](1)(_ * _.asInstanceOf[Cst].c)), nonCstFactors)
    }
  }
}


case class Sum private[arithmetic](terms: List[ArithExpr with SimplifiedExpr]) extends ArithExpr {
  Debug.Assert(terms.length > 1, s"Terms should have at least two terms in $toString")

  if (Debug.SanityCheck && simplified) {
    Debug.Assert(terms.view.zip(terms.tail).forall(x => ArithExpr.isCanonicallySorted(x._1, x._2)), "Terms should be sorted")
    terms.foreach(x => {
      Debug.AssertNot(x.isInstanceOf[Sum], "Sum cannot contain a Sum")
    })
  }

  override val HashSeed = 0x8e535130

  override lazy val digest: Int = terms.foldRight(HashSeed)((x, hash) => hash ^ x.digest())

  /* Factorises a sum smarter and slower than ComputeGCD.factorizeSum. Can deal with division.
   * Consider improving computeGCD and using it here.
   *
   * c*a + c*b  :  c * SimplifySum(a, b)
   */
  lazy val asProd: Option[Prod] = if (!NewFactorizationOfSum()) None else {
    // We should never have a sum with one term
    assume(terms.length > 1)

    // Convert each term into a list of factors (if a term is not a prod, the result will be a list of 1 element)
    val prodTerms: List[List[ArithExpr]] = terms.map {
      case Prod(factors) => factors
      case x => List(x)
    }

    val (cstCommonFactor: Cst, nonCstCommonFactors: List[ArithExpr]) =
      prodTerms.tail.foldLeft(Prod.partitionFactorsOnCst(prodTerms.head, simplified = true)) {
        case ((cstCommonFactorAcc: Cst, nonCstCommonFactorsAcc: List[ArithExpr]), nextTerm: List[ArithExpr]) =>
          SimplifySum.getCommonFactors(cstCommonFactorAcc, nonCstCommonFactorsAcc, nextTerm)
      }

    // First, remove all non-constant factors using simple matching
    val prodTermsWithoutCommonNonCstFactors: List[ArithExpr] = nonCstCommonFactors match {
      case Nil => // No common non-constant factors
        prodTerms.map(SimplifyProd(_))
      case _ =>
        prodTerms.map(prodTermFactors =>
          SimplifyProd(Prod.removeFactors(prodTermFactors, nonCstCommonFactors)))
    }

    // Then, remove the constant factor using division
    val prodTermsWithoutCommonFactors = prodTermsWithoutCommonNonCstFactors.map(_ /^ cstCommonFactor)

    // Finally, construct the common factor
    ((cstCommonFactor, nonCstCommonFactors) match {
      case (Cst(1), Nil) => None
      case (Cst(1), _) => Some(nonCstCommonFactors)
      case (_, Nil) => Some(List(cstCommonFactor))
      case _ => Some(cstCommonFactor +: nonCstCommonFactors)
    }) match {
      case None => None // We have found neither constant, nor non-constant common factors
      // The Prod below is not simplified and we don't want to simplify it because we are creating a non-normal "view" here
      case Some(commonFactors) =>
        Some(Prod(commonFactors :+ prodTermsWithoutCommonFactors.reduce(_ + _)))
    }
  }

  override def equals(that: Any): Boolean = that match {
    case s: Sum => terms.length == s.terms.length && terms.intersect(s.terms).length == terms.length
    case _ => false
  }

  override lazy val toString: String = {
    val m = if (terms.nonEmpty) terms.mkString("+") else ""
    "(" + m + ")"
  }

  /**
    * Remove a list of terms from the terms of the sum and returns either a Sum of the remaining terms or the only term
    * left.
    * Removing terms does not create new optimization opportunity, therefore the resulting sum is still simplified.
    */
  def withoutTerm(list: List[ArithExpr]): ArithExpr = {
    assert(simplified, "This function only works on simplified products")
    val rest: List[ArithExpr] = terms.diff(list)
    assert(rest.nonEmpty, "Cannot remove all factors from a product")
    if (rest.length == 1) rest.head
    else new Sum(rest) with SimplifiedExpr
  }

  lazy val cstTerm: Cst = {
    if (simplified) terms.find(_.isInstanceOf[Cst]).getOrElse(Cst(0)).asInstanceOf[Cst]
    else Cst(terms.filter(_.isInstanceOf[Cst]).foldLeft[Long](0)(_ + _.asInstanceOf[Cst].c))
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(terms.map(_.visitAndRebuild(f)).reduce(_ + _))
}

object Sum {
  // This is an empty extractor to support SimplifySum that tries to be safe when we represent
  // other classes as sums (we might want to do it in the future)
  def unapply(ae: Any): Option[List[ArithExpr with SimplifiedExpr]] = ae match {
    case aexpr: ArithExpr => aexpr match {
      case s: Sum => Some(s.terms)
      case _ => None
    }
    case _ => None
  }
}

// this is really the remainder and not modulo! (I.e. it implements the C semantics of modulo)
case class Mod private[arithmetic](dividend: ArithExpr with SimplifiedExpr, divisor: ArithExpr with SimplifiedExpr)
  extends ArithExpr {
  //override val HashSeed = 0xedf6bb88
  override val HashSeed = 0xedf6bb8

  override lazy val digest: Int = HashSeed ^ dividend.digest() ^ ~divisor.digest()

  override lazy val toString: String = s"($dividend % ($divisor))"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(dividend.visitAndRebuild(f) % divisor.visitAndRebuild(f))
}

object Mod {
  def unapply(ae: ArithExpr): Option[(ArithExpr with SimplifiedExpr, ArithExpr with SimplifiedExpr)] =
    ae match {
      case m: Mod => Some(m.dividend, m.divisor)
      case _ => None
    }
}

case class AbsFunction private[arithmetic](ae: ArithExpr with SimplifiedExpr) extends ArithExpr {
  override val HashSeed = 0x3570a2ce

  override lazy val digest: Int = HashSeed ^ ae.digest()

  override lazy val toString: String = "Abs(" + ae + ")"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(abs(ae.visitAndRebuild(f)))
}

object abs {
  def apply(ae: ArithExpr): ArithExpr with SimplifiedExpr = SimplifyAbs(ae)
}

case class FloorFunction private[arithmetic](ae: ArithExpr with SimplifiedExpr) extends ArithExpr {
  override val HashSeed = 0x558052ce

  override lazy val digest: Int = HashSeed ^ ae.digest()

  override lazy val toString: String = "Floor(" + ae + ")"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(floor(ae.visitAndRebuild(f)))
}

object floor {
  def apply(ae: ArithExpr): ArithExpr with SimplifiedExpr = SimplifyFloor(ae)
}

case class CeilingFunction private[arithmetic](ae: ArithExpr with SimplifiedExpr) extends ArithExpr {
  override val HashSeed = 0xa45d23d0

  override lazy val digest: Int = HashSeed ^ ae.digest()

  override lazy val toString: String = "Ceiling(" + ae + ")"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(ceil(ae.visitAndRebuild(f)))
}

object ceil {
  def apply(ae: ArithExpr): ArithExpr with SimplifiedExpr = SimplifyCeiling(ae)
}

/* Conditional operator. Behaves like the `?:` operator in C. */
case class IfThenElse (test: BoolExpr, t: ArithExpr with SimplifiedExpr, e: ArithExpr with SimplifiedExpr) extends ArithExpr {
  override val HashSeed = 0x32c3d095

  override lazy val digest: Int = HashSeed ^ test.digest ^ t.digest() ^ ~e.digest()

  override lazy val toString: String = s"( $test ? $t : $e )"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr = {
    f(ArithExpr.ifThenElse(test.visitAndRebuild(f:(ArithExpr) => ArithExpr), t.visitAndRebuild(f), e.visitAndRebuild(f)))
  }
}

/* This class is meant to be used as a superclass, therefore, it is not private to this package */
abstract case class ArithExprFunction(name: String, range: Range = RangeUnknown) extends ArithExpr with SimplifiedExpr {
  override val HashSeed = 0x3105f133

  override lazy val digest: Int = HashSeed ^ range.digest() ^ name.hashCode

  override lazy val toString: String = s"$name($range)"

  def freeVariables:Set[Var] = Set()

}

object ArithExprFunction {
  def getArithExprFuns(expr: ArithExpr): Set[ArithExprFunction] = {
    val exprFunctions = scala.collection.mutable.HashSet[ArithExprFunction]()
    ArithExpr.visit(expr, {
      case function: ArithExprFunction => exprFunctions += function
      case _ =>
    })
    exprFunctions.toSet
  }
}

class Lookup private[arithmetic](val table: Seq[ArithExpr with SimplifiedExpr],
                                 val index: ArithExpr with SimplifiedExpr, val id: Int)
  extends ArithExprFunction("lookup") {
  override lazy val digest: Int = HashSeed ^ table.hashCode ^ index.digest() ^ id.hashCode()

  override lazy val toString: String = "lookup" + id + "(" + index + ")"

  override def equals(that: Any): Boolean = that match {
    case thatLookup: Lookup => thatLookup.table == this.table &&
      thatLookup.index == this.index && thatLookup.id == this.id
    case _ => false
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr = {
    f(Lookup(table.map(_.visitAndRebuild(f)), index.visitAndRebuild(f), id))
  }
}

object Lookup {
  def apply(table: Seq[ArithExpr], index: ArithExpr, id: Int): ArithExpr with SimplifiedExpr =
    SimplifyLookup(table, index, id)
}

case class BitwiseXOR private[arithmetic](a: ArithExpr with SimplifiedExpr, b: ArithExpr with SimplifiedExpr)
  extends ArithExpr with SimplifiedExpr {
  override val HashSeed = 0x00000042

  override lazy val digest: Int = HashSeed ^ a.digest() ^ b.digest()

  override def toString: String = "(" + a + ")^(" + b + ")"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(a.visitAndRebuild(f) ^ b.visitAndRebuild(f))
}

case class BitwiseAND private[arithmetic](a: ArithExpr with SimplifiedExpr, b: ArithExpr with SimplifiedExpr)
  extends ArithExpr with SimplifiedExpr {
  override val HashSeed = 0x42424200
  override lazy val digest: Int = HashSeed ^ a.digest() ^ b.digest()

  override def toString: String = "(" + a + ")&(" + b + ")"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(a.visitAndRebuild(f) & b.visitAndRebuild(f))
}

case class LShift private[arithmetic](a: ArithExpr with SimplifiedExpr, b: ArithExpr with SimplifiedExpr)
  extends ArithExpr with SimplifiedExpr {
  override val HashSeed = 0x42420042
  override lazy val digest: Int = HashSeed ^ a.digest() ^ b.digest()

  override def toString: String = "(" + a + ")<<(" + b + ")"

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(a.visitAndRebuild(f) << b.visitAndRebuild(f))
}

/**
  * Represents a variable in the expression. A variable is an unknown term which is immutable within the expression
  * but its value may change between expression, like a variable in C.
  *
  * @param name  Name for the variable. Might be empty, in which case a name will be generated.
  * @param range Range of possible values for the variable.
  * @note The uniqueness of the variable name is not enforced since there is no notion of scope.
  *       Also note that the name is purely decorative during partial evaluation: the variable is actually tracked
  *       using an instance counter, hence multiple instances sharing the same name will not be simplified.
  */
class Var private[arithmetic](val name: String,
                              val range: Range = RangeUnknown,
                              val fixedId: Option[Long] = None) extends ArithExpr {
  override lazy val hashCode: Int = 8 * 79 + id.hashCode

  override val HashSeed = 0x54e9bd5e

  override lazy val digest: Int = HashSeed ^ name.hashCode ^ id.hashCode ^ range.digest()

  /**
    * Same functionality as clone(), but with a SimplifiedExpr trait.
    * This is used in SimplifyVar when recreating subclasses of Var; since Var is inherited from outside
    * the scope of this package (arithmetic), SimplifyVar cannot instantiate the subtypes itself and has to
    * do it through this public interface.
    *
    * @return A clone with the SimplifiedExpr trait
    */
  def cloneSimplified(): Var with SimplifiedExpr = new Var(name, range, Some(id)) with SimplifiedExpr

  override def equals(that: Any): Boolean = that match {
    case v: Var => this.id == v.id
    case _ => false
  }

  override lazy val toString = s"v_${name}_$id"

  lazy val toStringWithRange = s"$toString[${range.toString}]"

  val id: Long = {
    if (fixedId.isDefined)
      fixedId.get
    else {
      Var.incCnt
    }
  }

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr = {
    f(Var(name, range.visitAndRebuild(f), Some(id)))
  }

  def copy(r: Range) = new Var(name, r, Some(this.id))
}

object Var {
  private val cnt = new AtomicLong(-1) /* Instance counter */

  def incCnt() : Long = {
    var _id: Long = 0
    do {
      _id = Var.cnt.incrementAndGet()
      if (_id < 0)
       Var.cnt.compareAndSet(_id, 0)
    } while (_id < 0)
    _id
  }

  def apply(name: String = ""): Var = new Var(name)

  def apply(range: Range): Var = new Var("", range)

  def apply(name: String, range: Range): Var = new Var(name, range)

  def apply(name: String, range: Range, fixedId: Option[Long]): Var = new Var(name, range, fixedId)

  def unapply(v: Var): Option[(String, Range)] = Some((v.name, v.range))
}

class NamedVar (override val name: String, override val range: Range = RangeUnknown, override val fixedId: Option[Long] = None) extends Var(name, range, fixedId) {
  override lazy val hashCode = 8 * 79 + name.hashCode

  override val HashSeed = 0x54e9bd5e

  override lazy val digest: Int = HashSeed ^ name.hashCode ^ range.digest()

  override def equals(that: Any) = that match {
    case v: NamedVar => this.name == v.name
    case _ => false
  }

  override lazy val toString = s"$name"

  override lazy val toStringWithRange = s"$toString[${range.toString}]"

  override def copy(r: Range) = new NamedVar(name, r)

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr = {
    f(NamedVar(name, range.visitAndRebuild(f)))
  }

  override def cloneSimplified() = new NamedVar(name, range) with SimplifiedExpr
}

object NamedVar {
  def apply(name: String): NamedVar= new NamedVar(name)
  def apply(name: String, range: Range): NamedVar= new NamedVar(name, range)
}

object PosVar {
  def apply(name: String): Var = new Var(name, StartFromRange(Cst(0)))
}

object SizeVar {
  def apply(name: String): Var = new Var(name, StartFromRange(Cst(1)))
}

class OpaqueVar(val v: Var,
                r: Range = RangeUnknown,
                fixedId: Option[Long] = None) extends ExtensibleVar("", r, fixedId) {
  override def copy(r: Range) = new OpaqueVar(v, r, Some(this.id))

  override def cloneSimplified() = new OpaqueVar(v, r, Some(this.id)) with SimplifiedExpr

  override lazy val (min: ArithExpr, max: ArithExpr) = (this, this)
  override lazy val sign: Sign.Value = v.sign

  override lazy val isEvaluable = false

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr =
    f(new OpaqueVar(v, range.visitAndRebuild(f), Some(id)))
}

/* This class is ment to be used as a superclass, therefore, it is not private to this package */
abstract class ExtensibleVar(override val name: String,
                             override val range: Range = RangeUnknown,
                             fixedId: Option[Long] = None) extends Var(name, range, fixedId) {

  /* redeclare as abstract to force subclasses to implement */
  override def copy(r: Range): Var

  /* redeclare as abstract to force subclasses to implement */
  override def cloneSimplified(): Var with SimplifiedExpr

  override def visitAndRebuild(f: (ArithExpr) => ArithExpr): ArithExpr
}

case class BigSum private[arithmetic](variable:InclusiveIndexVar, body:ArithExpr) extends ArithExpr {
  val from: ArithExpr = variable.from
  val upTo:ArithExpr = variable.upTo

  override def HashSeed(): Int = 270493

  override def digest(): Int = this.HashSeed() ^ variable.digest ^ body.digest()

  override def visitAndRebuild(f: ArithExpr => ArithExpr): ArithExpr =
    BigSum(InclusiveIndexVar(variable.visitAndRebuild(f).asInstanceOf[NamedVar]), body.visitAndRebuild(f))

  override def toString: String = s"Σ{${variable.name} ∈ [${variable.from},${variable.upTo}] => $body}"

  def modify(newFrom:ArithExpr = this.from, newUpTo:ArithExpr = this.upTo, newBody:ArithExpr = this.body):ArithExpr = {
    BigSum(newFrom, newUpTo, `for`=this.variable, newBody)
  }
}

/**
  * A specialised form of NamedVar, where the Range is guaranteed to be a RangeAdd with steps of 1
  */
case class InclusiveIndexVar(override val name:String, from:ArithExpr, upTo:ArithExpr, override val fixedId: Option[Long] = None) extends NamedVar(name, RangeAdd(from, upTo + 1, 1), fixedId) {
  val rangeAdd:RangeAdd = this.range.asInstanceOf[RangeAdd]

  override def cloneSimplified: InclusiveIndexVar with SimplifiedExpr = new InclusiveIndexVar(name, from, upTo) with SimplifiedExpr
}

object InclusiveIndexVar {
  def apply(v:NamedVar):InclusiveIndexVar = {
    v match {
      case ok:InclusiveIndexVar => ok
      case _ => v.range match {
        case RangeAdd(start, stop, Cst(1)) =>  InclusiveIndexVar(v.name, start, stop)
        case _ => throw new Exception(s"Invalid conversion into inclusive index var from $v")
      }
    }
  }
}

object BigSum {
  def apply(from:ArithExpr, upTo:ArithExpr, makeBody:InclusiveIndexVar => ArithExpr):SimplifiedExpr = {
    val idxVar = InclusiveIndexVar("sumIdx", from, upTo) //Make sure start does not overlap stop?
    val bs = BigSum(idxVar, makeBody(idxVar))
    SimplifyBigSum(bs)
  }

  def apply(from:ArithExpr, upTo:ArithExpr, `for`:Var, in:ArithExpr):ArithExpr = {
    BigSum(from, upTo, makeBody = iv => ArithExpr.substitute(in, Map(`for` -> iv)))
  }
}

/**
  * This class represents a specialised chain of if then else statements, whose semantics rememble
  * v match {
  *   case 0 => cases(0)
  *   case 1 => cases(1)
  *   case _ => cases.last
  * }
  *
  * Big sum simplification makes use of this to implement the "if-then-else" peeling simplifications.
  * Always safe to transform this in a if-then-else chaine.
  */
final case class SteppedCase(v:NamedVar, cases:Seq[ArithExpr]) extends ArithExpr with SimplifiedExpr {
  override def HashSeed(): Int = 18022019

  override def digest(): Int = cases.foldRight(HashSeed)((x, hash) => hash ^ x.digest())


  override def visitAndRebuild(f: ArithExpr => ArithExpr): ArithExpr = {
    f(v) match {
        //We are replacing the steppedCase with a variable, that's fine
      case variable:Var =>
        SteppedCase(variable.asInstanceOf[NamedVar], cases.map(_.visitAndRebuild(f)))
      case _ =>
        //This makes no longer sense, the binder its not a variable.
        // Let's first turn this into an if statement, and then visit and rebuild that
        this.intoIfChain().visitAndRebuild(f)
    }
  }


  def intoIfChain():ArithExpr = {
    //Outermost guard
    ArithExpr.ifThenElse(v.lt(Cst(0)), Cst(0), bodyAsIf(this.cases, Cst(0)))
  }

  private def bodyAsIf(itemsLeft:Seq[ArithExpr], stepIndex:ArithExpr):ArithExpr = {
    itemsLeft.headOption match {
      case None => Cst(0)
      case Some(thisCase) => ArithExpr.ifThenElse(BoolExpr.arithPredicate(this.v, stepIndex, BoolExpr.ArithPredicate.Operator.==), thisCase,
        bodyAsIf(itemsLeft.tail, stepIndex + 1))
    }
  }
}

object SteppedCase {
  def apply(steps:ArithExpr*)(v:NamedVar):SteppedCase = new SteppedCase(v, steps.toVector)
}

