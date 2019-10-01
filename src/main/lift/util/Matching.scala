package lift.util

import scala.annotation.tailrec

case class Matching[A,B](f:A => Option[B])

object ListMatch {
  def apply[A,B](matchings:Matching[A,B]*):Matching[List[A], Map[Matching[A,B], B]] = {
    apply(matchings.toSeq)
  }

  def apply[A,B](matchings:Iterable[Matching[A,B]]):Matching[List[A], Map[Matching[A,B], B]] = {
    Matching(list => {
      val (found, leftovers) = Matching.matchMany(list, matchings)
      if(leftovers.isEmpty) {
        Some(found)
      } else None
    })
  }
}

object Matching {

  def just[A](f:A => Boolean):Matching[A, A] = Matching(x => Some(x).filter(f))

  def tryMatchFirst[A,B](items:Iterable[A], matching:Matching[A, B]):Option[(B, Iterable[A])] = tryMatchFirstRec(items, matching, Seq())

  def matchMany[A,B](items:Iterable[A], matchings: Iterable[Matching[A,B]]):(Map[Matching[A,B], B], Iterable[A]) =
    matchManyRec(items, matchings, Map(), Seq())


  @tailrec
  private def tryMatchFirstRec[A,B](items:Iterable[A], matching:Matching[A,B], accum:Seq[A]):Option[(B, Iterable[A])] =
    items.headOption match {
      case None => None
      case Some(item) => matching.f(item) match {
        case Some(x) => Some(x, accum ++ items.tail)
        case None => tryMatchFirstRec(items.tail, matching, accum :+ item)
      }
    }

  private def matchManyRec[A,B](items:Iterable[A], matchings:Iterable[Matching[A,B]], found:Map[Matching[A,B], B], leftovers:Seq[A]):(Map[Matching[A,B], B], Iterable[A]) = {
    matchings.headOption match {
      case None => (found, leftovers ++ items)
      case Some(matching) =>
        tryMatchFirst(items, matching) match {
          case None => matchManyRec(items, matchings.tail, found, leftovers)
          case Some((itemFound, restOfItems)) => matchManyRec(restOfItems, matchings.tail, found + (matching -> itemFound), leftovers)
        }
    }
  }
}