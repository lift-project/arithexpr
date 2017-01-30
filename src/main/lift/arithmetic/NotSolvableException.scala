package lift
package arithmetic

import scala.util.control.ControlThrowable

/**
  * Control flow exception used to abort arithmetic expression solving
  */
class NotSolvableException extends ControlThrowable
