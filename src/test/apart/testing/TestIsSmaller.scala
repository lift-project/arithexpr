package apart.testing

import apart.arithmetic._
import org.scalacheck.Properties
import org.scalacheck.Prop.{forAll, BooleanOperators}

import scala.language.implicitConversions

object TestIsSmaller extends Properties("IsSmaller") {

  import SupportForScalaCheck._

  /* ! a < a */
  property("irreflexivity") = forAll { (a: ArithExpr) =>
    !ArithExpr.isSmaller(a, a).getOrElse(false)
  }

  /* if (a < b) and (b < c) then (a < c) */
  property("transitivity") = forAll { (a: ArithExpr, b: ArithExpr, c: ArithExpr) =>
    val ab = ArithExpr.isSmaller(a, b)
    (ab.isDefined && ab.get) ==> {
      val bc = ArithExpr.isSmaller(b, c)
      (bc.isDefined && bc.get) ==> {
        val ac = ArithExpr.isSmaller(a, b)
        ac.isDefined && ac.get
      }
    }
  }

  /* if (a < b) then !(b < a) */
  property("asymmetry") = forAll { (a: ArithExpr, b: ArithExpr) =>
    val ab = ArithExpr.isSmaller(a, b)
    (ab.isDefined && ab.get) ==> {
      val ba = ArithExpr.isSmaller(b, a)
      ba.isDefined && !ba.get
    }
  }

  /* if (a < b) then (a + c < b + c) for all constants c */
  property("constant addition/subtraction") = forAll { (a: ArithExpr, b: ArithExpr, c: Cst) =>
    val ab = ArithExpr.isSmaller(a, b)
    (ab.isDefined && ab.get) ==> {
      val cabc = ArithExpr.isSmaller(a + c, b + c)
      cabc.isDefined && cabc.get
    }
  }


}
