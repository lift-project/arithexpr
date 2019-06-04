package lift.arithmetic

object ArithExprUtils {
  def removeAt[T](i: Int, from: List[T]): List[T] = from.take(i) ++ from.drop(i + 1)
  def replaceAt[T](i: Int, replacement: T, from: List[T]): List[T] = from.zipWithIndex.map(element =>
    if (element._2 == i) replacement else element._1)
}
