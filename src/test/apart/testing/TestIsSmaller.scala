package apart.testing

import apart.arithmetic._
import org.scalacheck.Properties
import org.scalacheck.Prop.{forAll, BooleanOperators}

import scala.language.implicitConversions

object TestIsSmaller extends Properties("IsSmaller") {

  import SupportForScalaCheck._

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

}
