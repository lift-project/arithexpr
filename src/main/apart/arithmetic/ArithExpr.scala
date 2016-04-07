package apart
package arithmetic

import java.util.concurrent.atomic.AtomicLong

import arithmetic.simplifier._
import ir.ast.Group

import scala.collection.immutable
import scala.language.implicitConversions
import scala.util.Random
import scala.util.control.ControlThrowable

/**
 * Sanity checks. These methods are used to check the sanity of simplified expressions as they are built.
 * They can be quite expensive since they traverse the list of terms and factors a few times for sums and prods.
 * If the expression evaluation starts to be noticeably slow, it should be disabled.
 */
object Debug {
  val SanityCheck = true

  def Assert(p: Boolean, reason: => String = "no reason"): Unit = {
    if(!p) throw new RuntimeException(s"Sanity check failed: $reason")
  }

  def AssertNot(p: Boolean, reason: => String = "no reason"): Unit = {
    if(p) throw new RuntimeException(s"Sanity check failed: $reason")
  }
}

/**
 * Control flow exception used to abort arithmetic expression evaluation on unknown terms.
 */
final class NotEvaluableException extends ControlThrowable

/**
 * Predicate object. Stores two arithmetic expressions and an operator
 */
case class Predicate(lhs: ArithExpr, rhs: ArithExpr, op: Predicate.Operator.Operator) {
  override lazy val toString: String = s"($lhs $op $rhs)"

  sealed class TrueBlock(predicate: Predicate, thenblock: ArithExpr) {
    def !!(els: ArithExpr) = SimplifyIfThenElse(predicate, thenblock, els)
  }

  def ??(thenblock: ArithExpr) = new TrueBlock(this, thenblock)

  val digest: Int =  0x7c6736c0 ^ lhs.digest() ^ rhs.digest() ^ op.hashCode()
}

object Predicate {
  /**
   * List of comparison operators
   */
  object Operator extends Enumeration {
    type Operator = Value
    val < = Value("<")
    val > = Value(">")
    val <= = Value("<=")
    val >= = Value(">=")
    val != = Value("!=")
    val == = Value("==")
  }
}

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
   * Flag set if the value might be negative. All variables are considered positive. If an expression contains a subtraction
   * or a negative constant, compute if the value might be negative.
   */
  lazy val might_be_negative: Boolean = true

  /**
   * Lower and upper bounds of the expression.
   */
  lazy val (min,max): (ArithExpr,ArithExpr) = (Var(""), Var(""))

  /**
   * Evaluates an arithmetic expression.
   * @return The Int value of the expression.
   * @throws NotEvaluableException if the expression cannot be fully evaluated.
   */
  lazy val eval: Int = {
    // Evaluating is quite expensive, traverse the tree to check assess evaluability
    if (!isEvaluable) throw ArithExpr.NotEvaluable
    val dblResult = ArithExpr.evalDouble(this)
    if (dblResult.isValidInt)
      dblResult.toInt
    else throw ArithExpr.NotEvaluable
  }

  lazy val isEvaluable: Boolean = {
    !ArithExpr.visitUntil(this, x => {
      x == ? || x.isInstanceOf[ArithExprFunction] || x.isInstanceOf[Var] || x.isInstanceOf[IfThenElse]
    })
  }

  lazy val evalDbl: Double = ArithExpr.evalDouble(this)

  lazy val atMax: ArithExpr = atMax(constantMax = false)

  def atMax(constantMax: Boolean = false): ArithExpr = {
    val vars = varList.filter(_.range.max != ?)
    val exprFunctions = ArithExprFunction.getArithExprFuns(this).filter(_.range.max != ?)
    var maxLens = vars.map(_.range.max) ++ exprFunctions.map(_.range.max)

    if (constantMax && !maxLens.exists(!_.isInstanceOf[Cst]))
      maxLens = maxLens.map(m => Cst(m.eval - 1))

    ArithExpr.substitute(this, (vars ++ exprFunctions, maxLens).zipped.toMap)
  }

  lazy val atMin: ArithExpr = {
    val vars = varList.filter(_.range.min != ?)
    val exprFunctions = ArithExprFunction.getArithExprFuns(this).filter(_.range.min != ?)
    val maxLens = vars.map(_.range.min) ++ exprFunctions.map(_.range.min)
    ArithExpr.substitute(this, (vars ++ exprFunctions, maxLens).zipped.toMap)
  }

  private def getVars(e: ArithExpr = this, l: Set[Var] = Set[Var]()) : Set[Var] = {
    e match {
      case adds: Sum => adds.terms.foldLeft(l)((acc,expr) => getVars(expr, acc))
      case muls: Prod => muls.factors.foldLeft(l)((acc,expr) => getVars(expr, acc))
      case Pow(b,oe) => l ++ getVars(b) ++ getVars(oe)
      case v: Var => l + v
      case _ => l
    }
  }

  lazy val varList = getVars()

  /**
   * Fast Equality operator.
   * The function first compares the seeds, then the digests. If they are equal, the trees are compared using the
   * full equality operator.
   * @param that Another expression.
   * @return True if the two expressions are equal, false otherwise.
   * @note This operator works only for simplified expressions.
   */
  def ==(that: ArithExpr): Boolean = {
    if (this.HashSeed() == that.HashSeed() && digest() == that.digest())
      this === that
    else false
  }

  /**
   * True equality operator. Compare each operands.
   * @param that Another expression.
   * @return True iif the two expressions are equal.
   * @note This operator works only for simplified expressions.
   */
  def ===(that: ArithExpr): Boolean = (this, that) match {
    case (Cst(x), Cst(y)) => x == y
    case (IntDiv(x1,y1), IntDiv(x2,y2)) => x1 == x2 && y1 == y2
    case (Pow(x1,y1), Pow(x2,y2)) => x1 == x2 && y1 == y2
    case (Log(x1,y1), Log(x2,y2)) => x1 == x2 && y1 == y2
    case (Mod(x1,y1), Mod(x2,y2)) => x1 == x2 && y1 == y2
    case (Floor(a), Floor(x)) => a == x
    case (Sum(a), Sum(b)) => a.length == b.length && (a zip b).forall(x => x._1 == x._2)
    case (Prod(a), Prod(b)) => a.length == b.length && (a zip b).forall(x => x._1 == x._2)
    case (IfThenElse(test1, t1, e1), IfThenElse(test2, t2, e2)) =>
      test1.op == test2.op && test1.lhs == test2.lhs && test1.rhs == test2.rhs && t1 == t2 && e1 == e2
    case (f1:ArithExprFunction, f2:ArithExprFunction) => f1.name == f2.name
    case (v1:Var, v2:Var) => v1.id == v2.id
    case _ =>
      System.err.println(s"$this and $that are not equal")
      false
  }

  /* === Arithmetic operators === */

  def pow(that: ArithExpr): ArithExpr = SimplifyPow(this, that)

  /**
   * Multiplication operator.
   * @param that Right-hand side.
   * @return An expression representing the product (not necessarily a Prod object).
   */
  def *(that: ArithExpr): ArithExpr = SimplifyProd(this,that)

  /**
   * Addition operator.
   * @param that Right-hand side.
   * @return An expression representing the sum (not necessarily a Sum object).
   */
  def +(that: ArithExpr): ArithExpr = SimplifySum(this,that)

  /**
   * Division operator in Natural set (ie int div like Scala): `1/2=0`.
   * @param that Right-hand side (divisor).
   * @return An IntDiv object wrapping the operands.
   * @throws ArithmeticException if the right-hand-side is zero.
   */
  def /(that: ArithExpr) = SimplifyIntDiv(this, that)

  /**
   * Ordinal division operator.
   * This prevents integer arithmetic simplification through exponentiation.
   * @param that Right-hand side (divisor).
   * @return The expression multiplied by the divisor exponent -1.
   */
  def /^(that: ArithExpr) = (this,that) match {
    case (x,Cst(1)) => x
    case (Cst(x),Cst(y)) if x % y == 0 => Cst(x/y)
    case (x,y) if x == y => Cst(1)
    case (x,y) if x == (y * Cst(-1)) => Cst(-1)
    case (x,y) => x * (y pow -1)
  }

  /**
   * Transform subtraction into sum of product with -1
   * @param that Right-hand side of the division
   * @return A Sum object
   */
  def -(that: ArithExpr) = this + (that * -1)

  /**
   * The % operator yields the remainder from the division of the first expression by the second.
   * @param that The right-hand side (divisor)
   * @return A Mod expression
   * @throws ArithmeticException if the right-hand-side is zero.
   * @note This operation is defined for negative number since it computes the remainder of the algebraic quotient
   *       without fractional part times the divisor, ie (a/b)*b + a%b is equal to a.
   */
  def %(that: ArithExpr) = SimplifyMod(this, that)

  /* === Comparison operators === */
  /**
   * Lower than comparison operator.
   * @param that Right-hand side of the comparison
   * @return A Predicate object
   */
  def lt(that: ArithExpr) = Predicate(this, that, Predicate.Operator.<)

  /**
   * Greater than comparison operator.
   * @param that Right-hand side of the comparison
   * @return A Predicate object
   */
  def gt(that: ArithExpr) = Predicate(this, that, Predicate.Operator.>)

  /**
   * Lower-or-equal comparison operator.
   * @param that Right-hand side of the comparison
   * @return A Predicate object
   */
  def le(that: ArithExpr) = Predicate(this, that, Predicate.Operator.<=)

  /**
   * Greater-or-equal comparison operator.
   * @param that Right-hand side of the comparison
   * @return A Predicate object
   */
  def ge(that: ArithExpr) = Predicate(this, that, Predicate.Operator.>=)

  /**
   * Equality comparison operator.
   * @note Silently overrides the reference comparison operator `AnyRef.eq`
   * @param that Right-hand side of the comparison
   * @return A Predicate object
   */
  def eq(that: ArithExpr) = Predicate(this, that, Predicate.Operator.==)

  /**
   * Inequality comparison operator.
   * @note Silently overrides the reference comparison operator `AnyRef.ne`
   * @param that Right-hand side of the comparison
   * @return A Predicate object
   */
  def ne(that: ArithExpr) = Predicate(this, that, Predicate.Operator.!=)

  /* == Hash function == */
  /**
   * The hash function creates a 32 bit digest of the expression. Each node type has a unique salt and combines
   * the hashes of the subexpressions using a commutative and associative operator (most likely XOR).
   *
   * The probability of a collision is already fairly low, but in order to guarantee equality one should call
   * visit with a hash comparison function on the sub-tree to guarantee that each node matches. The probability
   * of a collision is then the probability of a collision of a leaf node, which is zero for constant nodes and zero
   * for the first 2,147,483,647 variable instances.
   * @return A 32 bit digest of the expression.
   */
  def digest(): Int

  def HashSeed(): Int
}

object ArithExpr {

  implicit def IntToCst(i: Int): Cst = Cst(i)

  val NotEvaluable = new NotEvaluableException()

  def max(e1: ArithExpr, e2: ArithExpr) : ArithExpr = minmax(e1, e2)._2

  def min(e1: ArithExpr, e2: ArithExpr) : ArithExpr = minmax(e1, e2)._1

  val sort: (ArithExpr,ArithExpr) => Boolean = (x:ArithExpr, y:ArithExpr) =>
    x.HashSeed() < y.HashSeed() || (x.HashSeed() == y.HashSeed() && x.digest() < y.digest())

  def minmax(v: Var, c: Cst): (ArithExpr, ArithExpr) = {
    val m1 = v.range.min match { case Cst(min) => if (min >= c.c) Some((c, v)) else None; case _ => ??? }
    if (m1.isDefined) return m1.get

    val m2 = v.range.max match { case Cst(max) => if (max <= c.c) Some((v, c)) else None; case _ => ??? }
    if (m2.isDefined) return m2.get

    throw NotEvaluable
  }

  def minmax(p: Prod, c: Cst): (ArithExpr, ArithExpr) = {
    val lb = lowerBound(p)
    if (lb.isDefined && lb.get >= c.c) return (c, p)

    val ub = upperBound(p)
    if (ub.isDefined && ub.get <= c.c) return (p, c)

    throw NotEvaluable
  }

  /**
   * Find the Greatest Common Divisor in two expressions.
   * @param a The first expression.
   * @param b The second expression.
   * @return The greatest common divisor.
   */
  def gcd(a: ArithExpr, b: ArithExpr): ArithExpr = {
    // Factorize a sum: find a factor common to all terms
    def FactorizeSum(s: Sum): ArithExpr = {
      assert(s.terms.length > 1)
      val fac = (for {
        t1 <- s.terms
        t2 <- s.terms
        if t1.HashSeed < t2.HashSeed || (t1.HashSeed == t2.HashSeed && t1.digest < t2.digest)
      } yield gcd(t1,t2)).map{
        case c@Cst(1) => return c
        case x => x
      }
      if(fac.isEmpty) Cst(1)
      else fac.reduce(_+_)
    }

    val g: ArithExpr = (a,b) match {
      // GCD of constants
      case (Cst(x), Cst(y)) => if(y == 0) scala.math.abs(x) else gcd(scala.math.abs(y), scala.math.abs(x)%y)

      case (i:IntDiv, _) => Cst(1)

      // GCD of two identical things is itself
      case (x, y) if x == y => x

      // GCD of powers, go through bases and find a match, return smallest exp
      // TODO: handle negative exp
      case (Pow(_,Cst(x)), _) if x < 0 => Cst(1)
      case (_, Pow(_,Cst(x))) if x < 0 => Cst(1)
      case (x, Pow(ob,e)) if ob == x => x // pow 1 (implicit)
      case (Pow(b1,e1), Pow(b2,e2)) if b1 == b2 => b1 pow ArithExpr.min(e1, e2)
      case (Pow(ob,e), Prod(factors)) if factors.contains(ob) => ob // pow 1 (implicit)
      case (Prod(factors), Pow(ob,e)) if factors.contains(ob) => ob // pow 1 (implicit)
      case (Pow(ob,e), x) if ob == x => x // pow 1 (implicit)
      case (x, Pow(ob,e)) if ob == x => x // pow 1 (implicit)

      // GCD of products: find GCD in factor pairs
      case (Prod(fs1), Prod(fs2)) => (for { f1 <- fs1; f2 <- fs2 } yield gcd(f1,f2)).reduce(_*_)
      case (Prod(f), c:Cst) => gcd(b,a)
      case (c:Cst, Prod(f)) => f.find(_.isInstanceOf[Cst]) match {
        case Some(x) => gcd(c,x)
        case _ => Cst(1)
      }
      case (Prod(f), x) if f.contains(x) && !ArithExpr.hasDivision(f) => x
      case (x, Prod(f)) if f.contains(x) && !ArithExpr.hasDivision(f) => x

      // GCD of sums: find common factor across all terms
      case (s1:Sum, s2:Sum) =>
        // Compute the common factors
        val fac1 = FactorizeSum(s1)
        if (fac1 == Cst(1)) return fac1
        val fac2 = FactorizeSum(s2)
        if (fac1 == Cst(1)) return fac2

        // The GCD could be either the factor or the remainder, so we compute the intersection
        val common = List(fac1, s1 /^ fac1).intersect(List(fac2, s2 /^ fac2))
        if(common.isEmpty) Cst(1)
        else common.head

      case (x, s:Sum) => gcd(b,a)
      case (s:Sum, x) =>
        // compute the common factor
        val factor = FactorizeSum(s)
        // If there is none, there is no possible common factor
        if (factor == Cst(1)) factor
        // otherwise see if there is a common factor with the sum's terms
        else gcd(factor, x) match {
          // If there isn't, we still have a chance with the remainder
          //case Cst(x) if x == 1 => gcd(x, s /^ factor)
          case x => x
        }

      case (x,y) => Cst(1)
    }
    // Never factorize by a fraction
    g match {
      case Pow(x,Cst(-1)) => Cst(1)
      case i:IntDiv => Cst(1)
      case x => x
    }
  }

  private def upperBound(p: Prod): Option[Int] = {
    Some(Prod(p.factors.map({
      case v: Var => v.range.max match {
        case max: Cst => max
        case _ => return None
      }
      case c: Cst => c
      case _ => throw new IllegalArgumentException("upperBound expects a Var or a Cst")
    })).eval)
  }

  private def lowerBound(p: Prod): Option[Int] = {
    Some(Prod(p.factors.map({
      case v: Var => v.range.min match {
        case min: Cst => min
        case _ => return None
      }
      case c: Cst => c
      case _ => throw new IllegalArgumentException("lowerBound expects a Var or a Cst")
    })).eval)
  }

  def minmax(e1: ArithExpr, e2: ArithExpr): (ArithExpr, ArithExpr) = {
    e1 - e2 match {
      case Cst(c) if c < 0 => (e1, e2) /* e1 is smaller than e2 */
      case Cst(c) => (e2, e1) /* e2 is smaller than e1*/
      case _ =>
        (e1, e2) match {
          case (v: Var, c: Cst) => minmax(v, c)
          case (c: Cst, v: Var) => minmax(v, c).swap

          case (p: Prod, c: Cst) => minmax(p, c)
          case (c: Cst, p: Prod) => minmax(p, c).swap

          case _ => throw NotEvaluable
        }
    }
  }

  def max(e: ArithExpr) : ArithExpr = minmax(e)._2

  def min(e: ArithExpr) : ArithExpr = minmax(e)._1

  def minmax(e: ArithExpr): (ArithExpr, ArithExpr) = {
    e match {
      case _: Cst => (e, e)
      case Var(_, range) => ( if (range.min != ?) min(range.min) else e,
                              if (range.max != ?) max(range.max) else e )

      case Sum(sums) => ( Sum(sums.map(min)), Sum(sums.map(max)) )

      // TODO: check if the product is positive or negative
      case Prod (prods) => ( prods.map(min).reduce(_*_), prods.map(max).reduce(_*_) )

      case Pow(b, cst@Cst(c)) => ( if (c>=0) min(b) pow cst else max(b) pow cst,
                                   if (c>=0) max(b) pow cst else min(b) pow cst )

      case _ =>  throw NotEvaluable
    }
  }

  def contains(expr: ArithExpr, elem: ArithExpr) : Boolean = {
    visit(expr, e => if (e==elem) return true)
    false
  }

  /**
   * Find if an expression is possibly a multiple of another.
   * @param expr The expression.
   * @param that A possible multiple.
   * @return True if `that` is a multiple of `expr`, false otherwise
   */
  def multipleOf(expr: ArithExpr, that: ArithExpr) : Boolean = (ExprSimplifier(expr), that) match {

    // Compare two products, look for inclusion of common denominator
    case (Prod(terms), Prod(otherTerms)) => terms.count(isDivision) == otherTerms.count(isDivision) && otherTerms.map({
        case pow: Pow => terms.exists(multipleOf(_, pow))
        case x => terms.contains(x)
      }).reduce(_&&_)

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
    case (x,y) => x == y
  }

  private[arithmetic] def hasDivision(factors: List[ArithExpr]): Boolean = {
    factors.exists(isDivision)
  }

  private[arithmetic] def isDivision: (ArithExpr) => Boolean = {
    case Pow(_, Cst(x)) if x < 0 => true
    case e => false
  }

  def isSmaller(ae1: ArithExpr, ae2: ArithExpr): Boolean = {
    //System.err.println(s"${ae1} <?< ${ae2}")
    try {
      // TODO: Assuming range.max is non-inclusive
      val atMax = ae1.atMax

      atMax match {
        case Prod(factors) if hasDivision(factors) =>
          val newProd = factors.filter(!isDivision(_)).reduce(_*_)
          if (newProd == ae2)
            return true
        case _ =>
      }

      if (atMax == ae2 || ae1.atMax(constantMax = true).eval < ae2.eval)
        return true
    } catch {
      case e: NotEvaluableException =>
    }
    false
  }

  def visit(e: ArithExpr, f: (ArithExpr) => Unit) : Unit = {
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
      case Log(b,x) =>
        visit(b, f)
        visit(x, f)
      case Floor(expr) => visit(expr, f)
      case Sum(terms) => terms.foreach(t => visit(t, f))
      case Prod(terms) => terms.foreach(t => visit(t, f))
      case IfThenElse(test, t, e) => {
        visit(test.lhs, f)
        visit(test.rhs, f)
        visit(t, f)
        visit(t, f)
      }
      case Var(_,_) |  Cst(_) | ArithExprFunction(_,_) =>
      case x if x.getClass == ?.getClass =>
      case _ => throw new RuntimeException(s"Cannot visit expression $e")
    }
  }

  def visitUntil(e: ArithExpr, f: (ArithExpr) => Boolean) : Boolean = {
    if(f(e)) true
    else {
      e match {
        case Pow(base, exp) =>
          visitUntil(base, f) || visitUntil(exp, f)
        case IntDiv(n, d) =>
          visitUntil(n, f) || visitUntil(d, f)
        case Mod(dividend, divisor) =>
          visitUntil(dividend, f) || visitUntil(divisor, f)
        case Log(b,x) =>
          visitUntil(b, f) || visitUntil(x, f)
        case Floor(expr) => visitUntil(expr, f)
        case Sum(terms) =>
          terms.foreach(t => if (visitUntil(t, f)) return true)
          false
        case Prod(terms) =>
          terms.foreach(t => if (visitUntil(t, f)) return true)
          false
        case Var(_,_) |  Cst(_) | IfThenElse(_,_,_) | ArithExprFunction(_,_) => false
        case x if x.getClass == ?.getClass => false
        case _ => throw new RuntimeException(s"Cannot visit expression $e")
      }
    }
  }

  def substitute(e: ArithExpr, substitutions: scala.collection.immutable.Map[ArithExpr,ArithExpr]) : ArithExpr =
    substitutions.getOrElse(e, e) match {
      case Pow(l,r) => substitute(l,substitutions) pow substitute(r,substitutions)
      case IntDiv(n, d) => substitute(n, substitutions) / substitute(d, substitutions)
      case Mod(dividend, divisor) => substitute(dividend, substitutions) % substitute(divisor, substitutions)
      case Log(b,x) => Log(substitute(b, substitutions), substitute(x, substitutions))
      case IfThenElse(i, t, e) =>
        val cond = Predicate(substitute(i.lhs, substitutions), substitute(i.rhs, substitutions), i.op)
        cond ?? substitute(t, substitutions) !! substitute(e, substitutions)
      case Floor(expr) => Floor(substitute(expr, substitutions))
      case adds: Sum => adds.terms.map(t => substitute(t, substitutions)).reduce(_+_)
      case muls: Prod => muls.factors.map(t => substitute(t, substitutions)).reduce(_*_)
      case gc: GroupCall => new GroupCall(gc.group, substitute(gc.innerAe, substitutions))
      case x => x
    }

  private def evalDouble(e: ArithExpr) : Double = e match {
    case Cst(c) => c

    case IntDiv(n, d) => scala.math.floor(evalDouble(n) / evalDouble(d))

    case Pow(base,exp) => scala.math.pow(evalDouble(base),evalDouble(exp))
    case Log(b,x) => scala.math.log(evalDouble(x)) / scala.math.log(evalDouble(b))

    case Mod(dividend, divisor) => dividend.eval % divisor.eval

    case Sum(terms) => terms.foldLeft(0.0)((result,expr) => result+evalDouble(expr))
    case Prod(terms) => terms.foldLeft(1.0)((result,expr) => result*evalDouble(expr))

    case Floor(expr) => scala.math.floor(evalDouble(expr))

    case _ => throw NotEvaluable
  }


  def toInt(e: ArithExpr): Int = ExprSimplifier(e) match {
    case Cst(i) => i
    case _ => throw NotEvaluable
  }


  def asCst(e: ArithExpr) = ExprSimplifier(e) match {
    case c:Cst => c
    case _ => throw new IllegalArgumentException
  }

  /**
   * Math operations derived from the basic operations
   */
  object Math {

    /**
     * Computes the minimal value between the two argument
     * @param x The first value
     * @param y The second value
     * @return The minimum between x and y
     */
    def Min(x: ArithExpr, y: ArithExpr) = {
      // Since Min duplicates the expression, we simplify it in place to point to the same node
      val sx = ExprSimplifier(x)
      val sy = ExprSimplifier(y)
      (sx le sy) ?? sx !! sy
    }

    /**
     * Computes the maximal value between the two argument
     * @param x The first value
     * @param y The second value
     * @return The maximum between x and y
     */
    def Max(x: ArithExpr, y: ArithExpr) = {
      // Since Max duplicates the expression, we simplify it in place to point to the same node
      val sx = ExprSimplifier(x)
      val sy = ExprSimplifier(y)
      (sx gt sy) ?? sx !! sy
    }

    /**
     * Clamps a value to a given range
     * @param x The input value
     * @param min Lower bound of the range
     * @param max Upper bound of the range
     * @return The value x clamped to the interval [min,max]
     */
    def Clamp(x: ArithExpr, min: ArithExpr, max: ArithExpr) = Min(Max(x,min),max)

    /**
     * Computes the absolute value of the argument
     * @param x The input value
     * @return |x|
     */
    def Abs(x: ArithExpr) = (x lt Cst(0)) ?? (Cst(0)-x) !! x
  }

  def cardinal_id = 0
}

/**
 * ? represents an unknown value.
 */
case object ? extends ArithExpr with SimplifiedExpr {

  override val HashSeed = 0x3fac31

  override val digest: Int = HashSeed

  override lazy val might_be_negative = true

  override def ==(that: ArithExpr): Boolean = that.getClass == this.getClass
}

case class Cst(c: Int) extends ArithExpr with SimplifiedExpr {

  /**
   * Lower and upper bounds of a constant are itself.
   */
  override lazy val (min,max): (ArithExpr, ArithExpr) = (this, this)

  override lazy val toString = c.toString

  override val HashSeed = Integer.hashCode(c)

  override lazy val digest: Int =  Integer.hashCode(c)

  override lazy val might_be_negative = c < 0
}


case class IntDiv(numer: ArithExpr, denom: ArithExpr) extends ArithExpr() {

  // Check that the denominator is not 0
  if(denom == Cst(0))
    throw new ArithmeticException()

  override def toString: String = s"($numer) / ($denom)"

  /**
   * Upper bound of the expression: for a fraction:
   *  - the minimal value is the smallest possible numerator divided by the greatest possible denominator
   *  - the maximal value is the greatest possible numerator divided by the smallest possible denominator
   */
  override lazy val (min,max): (ArithExpr, ArithExpr) = {
    ExprSimplifier(numer.max - denom.min) match {
      case Cst(x) if x < 0 => (Cst(0), Cst(0))
      case _ =>
        denom.min match {
          case Cst(0) => (Cst(0), ExprSimplifier(numer.max / denom.min))
          case _ => (ExprSimplifier(numer.min / denom.max), ExprSimplifier(numer.max / denom.min))
        }
    }
  }

  override val HashSeed = 0xf233de5a

  override lazy val digest: Int = HashSeed ^ numer.digest() ^ ~denom.digest()

  override lazy val might_be_negative = numer.might_be_negative || denom.might_be_negative
}

case class Pow(b: ArithExpr, e: ArithExpr) extends ArithExpr {
  /**
   * Lower and upper bounds of the expression
   */
  override lazy val (min,max): (ArithExpr,ArithExpr) = {
    (b.min, b.max, e.min, e.max) match {
      case (Cst(x), Cst(y), Cst(a), Cst(b)) if x == y && a == b =>
        // If exponent and value are single point, emit single point
        val point = Cst(x) pow Cst(a)
        (point, point)
      case (Cst(x), Cst(y), Cst(a), Cst(ob)) if x >= 0 && y >=0 && a > 0 && ob > 0 =>
        // If the value is positive and the exponent is strictly positive, pow is monotonically increasing
        (Cst(x) pow Cst(a), Cst(y) pow Cst(ob))
      case (Cst(x), Cst(y), Cst(a), Cst(ob)) if x >= 0 && y >=0 && a < 0 && ob < 0 =>
        // If the value is positive and the exponent is strictly negative, pow is monotonically decreasing
        (Cst(y) pow Cst(a), Cst(x) pow Cst(ob))
      case x =>
        // Otherwise it could be anything
        (Var(""), Var(""))
    }
  }

  override def toString : String = e match {
    case Cst(-1) => "1/^("+b+")"
    case _ => "pow("+b+","+e+")"
  }

  override val HashSeed = 0x63fcd7c2

  override lazy val digest: Int = HashSeed ^ b.digest() ^ e.digest()

  override lazy val might_be_negative = b.might_be_negative
}

case class Log(b: ArithExpr, x: ArithExpr) extends ArithExpr with SimplifiedExpr {
  override def toString: String = "log"+b+"("+x+")"

  override val HashSeed = 0x370285bf

  override lazy val digest: Int = HashSeed ^ b.digest() ^ ~x.digest()

  override lazy val might_be_negative = b.might_be_negative
}



/**
 * Represent a product of two or more expressions.
 * @param factors The list of factors. The list should contain at least 2 operands and should not contain other products.
 */
case class Prod private[arithmetic] (factors: List[ArithExpr]) extends ArithExpr {

  if (Debug.SanityCheck && simplified) {
    Debug.Assert(factors.view.zip(factors.tail).forall(x => ArithExpr.sort(x._1,x._2)), "Factors should be sorted")
    Debug.Assert(factors.length > 1, s"Factors should have at least two terms in $toString")
    factors.foreach(x => {
      Debug.AssertNot(x.isInstanceOf[Prod], s"Prod cannot contain a Prod in $toString")
      Debug.AssertNot(x.isInstanceOf[Sum], "Prod should not contain a Sum")
    })
  }

  // Refine the equality operator to compare factors
  // TODO: Has false positives!!
//  override def ==(that: ArithExpr): Boolean = that match {
//    case Prod(otherfactors) =>
//      if(otherfactors.length != factors.length) return false
//      factors.map(_.digest()).sortWith(_<_) == otherfactors.map(_.digest()).sortWith(_<_)
//    case _ => false
//  }

  // TODO(tlutz): product depends on sign, should compute magnitude and sign independently
  override lazy val (min,max): (ArithExpr,ArithExpr) =
    (ExprSimplifier(factors.reduceLeft(_.min * _.min)), ExprSimplifier(factors.reduceLeft(_.max * _.max)))

  override def equals(that: Any) = that match {
    case p: Prod => factors.length == p.factors.length && factors.intersect(p.factors).length == factors.length
    case _ => false
  }

  override lazy val toString : String = {
    val m = if (factors.nonEmpty) factors.mkString("*") else {""}
    "(" + m +")"
  }

  def contains(e: ArithExpr): Boolean = factors.contains(e)

  override def hashCode(): Int = digest

  override lazy val digest: Int = factors.foldRight(HashSeed)((x,hash) => hash ^ x.digest())

  override val HashSeed = 0x286be17e

  /**
   * Remove a single factor from the list of factors and return either a Product of the factor left.
   * Removing a factor does not create new optimization opportunity, therefore the resulting prod is still simplified.
   */
  def withoutFactors(list: List[ArithExpr]): ArithExpr = {
    assert(simplified, "This function only works on simplified products")
    val rest = factors.diff(list)
    // If we took all the elements out, return neutral (1 for product)
    if (rest.isEmpty) Cst(1)
    // If there is only one left, return it
    else if (rest.length == 1) rest.head
    // Otherwise create a new product, which is also simplified by construction
    else new Prod(rest) with SimplifiedExpr
  }

  /**
   * Short-hand to remove a single factor
   */
  def withoutFactor(factor: ArithExpr): ArithExpr = withoutFactors(List(factor))

  /**
   * The constant factor of the product
   */
  lazy val cstFactor: Cst = {
    if (simplified) factors.find(_.isInstanceOf[Cst]).getOrElse(Cst(1)).asInstanceOf[Cst]
    else Cst(factors.filter(_.isInstanceOf[Cst]).foldLeft[Int](1)(_ + _.asInstanceOf[Cst].c))
  }

  lazy val isNegatedTerm = cstFactor == Cst(-1)

  override lazy val might_be_negative = factors.exists(_.might_be_negative)
}





case class Sum private[arithmetic] (terms: List[ArithExpr]) extends ArithExpr {

  if (Debug.SanityCheck && simplified) {
    Debug.Assert(terms.view.zip(terms.tail).forall(x => ArithExpr.sort(x._1,x._2)), "Terms should be sorted")
    Debug.Assert(terms.length > 1, s"Terms should have at least two terms in $toString")
    terms.foreach(x => {
      Debug.AssertNot(x.isInstanceOf[Sum], "Sum cannot contain a Sum")
    })
  }

  // Refine the equality operator to compare terms
  // TODO: Has false positives!!
//  override def ==(that: ArithExpr): Boolean = that match {
//    case Sum(otherterms) =>
//      if(otherterms.length != terms.length) return false
//      terms.map(_.digest()).sortWith(_<_) == otherterms.map(_.digest()).sortWith(_<_)
//    case _ => false
//  }

  override lazy val (min,max): (ArithExpr,ArithExpr) =
    (ExprSimplifier(terms.reduceLeft(_.min + _.min)), ExprSimplifier(terms.reduceLeft(_.max + _.max)))

  override def equals(that: Any) = that match {
    case s: Sum => terms.length == s.terms.length && terms.intersect(s.terms).length == terms.length
    case _ => false
  }

  override def hashCode(): Int = digest

  override lazy val toString: String = {
    val m = if (terms.nonEmpty) terms.mkString("+") else {""}
    "(" + m +")"
  }

  /**
   * Remove a single factor from the list of factors and return either a Sum of the only term left.
   * Removing a term does not create new optimization opportunity, therefore the resulting sum is still simplified.
   */
  def withoutTerm(list: List[ArithExpr]): ArithExpr = {
    assert(simplified, "This function only works on simplified products")
    val rest = terms.diff(list)
    assert(rest.nonEmpty, "Cannot remove all factors from a product")
    if (rest.length == 1) rest.head
    else new Sum(rest) with SimplifiedExpr
  }

  override val HashSeed = 0x8e535130

  override lazy val digest: Int = terms.foldRight(HashSeed)((x,hash) => hash ^ x.digest())

  lazy val cstTerm: Cst = {
    if (simplified) terms.find(_.isInstanceOf[Cst]).getOrElse(Cst(0)).asInstanceOf[Cst]
    else Cst(terms.filter(_.isInstanceOf[Cst]).foldLeft[Int](0)(_ + _.asInstanceOf[Cst].c))
  }

  override lazy val might_be_negative = terms.exists(_.might_be_negative)
}

case class Mod(dividend: ArithExpr, divisor: ArithExpr) extends ArithExpr {
  override lazy val min: ArithExpr = {
    (dividend.min,divisor.min) match {
      case (Cst(0),a) => Cst(0)
      case (a,b) => Cst(1) - b
    }
  }

  override lazy val max: ArithExpr = ExprSimplifier(divisor.max - 1)

  override lazy val toString: String = s"($dividend % ($divisor))"

  override val HashSeed = 0xedf6bb88

  override lazy val digest: Int = HashSeed ^ dividend.digest() ^ ~divisor.digest()

  override lazy val might_be_negative = dividend.might_be_negative
}

case class Floor(ae : ArithExpr) extends ArithExpr {
  override lazy val toString: String = "Floor(" + ae + ")"

  override val HashSeed = 0x558052ce

  override lazy val digest: Int = HashSeed ^ ae.digest()

  override lazy val might_be_negative = ae.might_be_negative
}

/**
 * Conditional operator. Behaves like the `?:` operator in C.
 * @param test A Predicate object.
 * @param t The 'then' block.
 * @param e The 'else block.
 */
case class IfThenElse(test: Predicate, t : ArithExpr, e : ArithExpr) extends ArithExpr {
  override lazy val toString: String = s"( $test ? $t : $e )"

  override val HashSeed = 0x32c3d095

  override lazy val digest: Int = HashSeed ^ test.digest ^ t.digest() ^ ~e.digest()
}

case class ArithExprFunction(name: String, var range: Range = RangeUnknown) extends ArithExpr with SimplifiedExpr {
  override lazy val digest: Int = HashSeed ^ range.digest() ^ name.hashCode

  override val HashSeed = 0x3105f133

  override lazy val toString: String = s"$name($range)"

  /**
   * TODO(tlutz): This is true for now but probably too restrictive
   */
  override lazy val might_be_negative = false
}

class GroupCall(val group: Group,
                val innerAe: ArithExpr) extends ArithExprFunction("group") {
  override lazy val toString: String = "groupComp" + group.id + "(" + innerAe + ")"
}

/**
 * Represents a variable in the expression. A variable is an unknown term which is immutable within the expression
 * but its value may change between expression, like a variable in C (cf sequence point).
 * @param name Identifier for the variable. Might be empty, in which case a name will be generated.
 * @param range Range of possible values for the variable.
 * @note The uniqueness of the variable name is not enforced since there is no notion of scope.
 *       Also note that the name is purely decorative during partial evaluation: the variable is actually tracked
 *       using an instance counter, hence multiple instances sharing the same name will not be simplified.
 */
case class Var(name: String, var range : Range = RangeUnknown) extends ArithExpr with SimplifiedExpr {

  override lazy val (min,max): (ArithExpr, ArithExpr) = (this,this)

  /** Unique identifier. */
  val id: Long = {
    var _id: Long = 0
    do {
      _id = Var.cnt.incrementAndGet()
      if(_id < 0)
        Var.cnt.compareAndSet(_id, 0)
    } while(_id < 0);
    _id;
  }

  override def equals(that: Any) = that match {
    case v: Var => this.id == v.id
    case _ => false
  }

  override lazy val hashCode = 8 * 79 + id.hashCode

  def updateRange(func: (Range) => Range): Unit = {
    if (range != RangeUnknown) {
      range = func(range)
    }
  }

  override val HashSeed =  0x54e9bd5e

  override lazy val digest: Int = HashSeed /*^ name.hashCode*/ ^ id.hashCode ^ range.digest()

  override lazy val might_be_negative = false

  override lazy val toString = "v_" + name + "_" + id
}




/* ==  Companion objects == */
object ArithExprFunction {

  def getArithExprFuns(expr: ArithExpr) : Set[ArithExprFunction] = {
    val exprFunctions = scala.collection.mutable.HashSet[ArithExprFunction]()
    ArithExpr.visit(expr, {
      case function: ArithExprFunction => exprFunctions += function
      case _ =>
    })
    exprFunctions.toSet
  }
}

object Var {
  /**
   * Instance counter
   */
  private val cnt = new AtomicLong(-1)

  def apply(range : Range) : Var = new Var("", range)

  def setVarsAtRandom(vars : Set[Var]) : scala.collection.immutable.Map[Var, Cst] = {

    var changed = false
    var substitutions : immutable.Map[Var, Cst] = new immutable.HashMap[Var, Cst]()
    var newVars : Set[Var] = vars

    do {
      changed = false

      // create a map of variable substitution
      val newSubsts : immutable.HashMap[Var, Cst] = newVars.foldLeft(immutable.HashMap[Var, Cst]())((map,v) => v.range match {
        case RangeAdd(Cst(start), Cst(stop), Cst(step)) => map+ (v -> Cst(Random.nextInt((stop - start) / step + 1) * step + start))
        case RangeMul(Cst(start), Cst(stop), Cst(mul))  => map+ (v -> Cst(start * math.pow(mul,Random.nextInt((math.log(stop / start) / math.log(mul) + 1).toInt)).toInt))
        case _ => map
      })

      if (newSubsts.nonEmpty)
        changed = true
      substitutions = substitutions ++ newSubsts

      // remove from the set of variables the ones which have a substitution
      newVars = newVars-- newSubsts.keySet

      // apply the substitutions in the range of each variable
      newVars.map(v => {
        v.range match {
          case RangeAdd(start, stop, step) => v.range = RangeAdd(
            ArithExpr.substitute(start, newSubsts.toMap),
            ArithExpr.substitute(stop, newSubsts.toMap),
            ArithExpr.substitute(step, newSubsts.toMap))
          case RangeMul(start, stop, step) => v.range = RangeMul(
            ArithExpr.substitute(start, newSubsts.toMap),
            ArithExpr.substitute(stop, newSubsts.toMap),
            ArithExpr.substitute(step, substitutions.toMap))
          case _ =>
        }
        v
      })
    } while (changed)

    substitutions
  }
}

object SizeVar {
  def apply(name: String): Var = new Var(name, StartFromRange(Cst(1))){
    override lazy val min = Cst(1)
  }
}

trait SimplifiedExpr extends ArithExpr {
  override val simplified = true
}
