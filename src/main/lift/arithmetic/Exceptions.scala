package lift.arithmetic

import scala.util.control.ControlThrowable

/**
  * Control flow exception used to abort arithmetic expression evaluation on unknown terms.
  */
case class NotEvaluableException() extends ControlThrowable

/**
  * Control flow exception used to abort arithmetic expression evaluation when evaluating to a value larger than an Int.
  */
case class NotEvaluableToIntException() extends ControlThrowable

/**
  * Control flow exception used to abort arithmetic expression solving
  */
case class NotSolvableException() extends ControlThrowable

