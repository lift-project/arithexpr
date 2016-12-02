package lift
package arithmetic

import scala.util.control.ControlThrowable

/**
  * Control flow exception used to abort arithmetic expression evaluation on unknown terms.
  */
object NotEvaluableException extends ControlThrowable
