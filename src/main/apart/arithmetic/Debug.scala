package apart
package arithmetic

object Debug {
  /**
    * Sanity checks. These methods are used to check the sanity of simplified expressions as they are built.
    * They can be quite expensive since they traverse the list of terms and factors a few times for sums and prods.
    * If the expression evaluation starts to be noticeably slow, it should be disabled.
    */
  val SanityCheck = true

  def Assert(p: Boolean, reason: => String = "no reason"): Unit = {
    if(!p) throw new RuntimeException(s"Sanity check failed: $reason")
  }

  def AssertNot(p: Boolean, reason: => String = "no reason"): Unit = {
    if(p) throw new RuntimeException(s"Sanity check failed: $reason")
  }
}
