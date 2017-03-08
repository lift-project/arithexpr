package lift.arithmetic

import scala.util.control.ControlThrowable

/**
  * Control flow exception used to abort arithmetic expression evaluation
  * on unknown terms.
  */
abstract case class NotEvaluableException private () extends ControlThrowable

/**
  * Companion object for `NotEvaluableException`.
  * Use `NotEvaluableException.NotEvaluable` when throwing.
  * Allows for easier debugging while not calling the constructor in the general case.
  */
object NotEvaluableException {
  val NotEvaluable = new NotEvaluableException() {}
}

/**
  * Control flow exception used to abort arithmetic expression evaluation
  * when evaluating to a value larger than an Int.
  */
abstract case class NotEvaluableToIntException private () extends ControlThrowable

/**
  * Companion object for `NotEvaluableToIntException`.
  * Use `NotEvaluableToIntException.NotEvaluableToInt` when throwing.
  * Allows for easier debugging while not calling the constructor in the general case.
  */
object NotEvaluableToIntException {
  val NotEvaluableToInt = new NotEvaluableToIntException() {}
}

/**
  * Control flow exception used to abort arithmetic expression solving
  */
abstract case class NotSolvableException private () extends ControlThrowable

/**
  * Companion object for `NotSolvableException`.
  * Use `NotSolvableException.NotSolvable` when throwing.
  * Allows for easier debugging while not calling the constructor in the general case.
  */
object NotSolvableException {
  val NotSolvable = new NotSolvableException() {}
}
