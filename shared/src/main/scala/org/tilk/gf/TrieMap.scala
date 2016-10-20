package org.tilk.gf

import scala.collection.generic._
import scala.collection.mutable.MapBuilder
import scala.collection.immutable.{AbstractMap, Map, MapLike, SortedMap}

final class TrieMap[A : Ordering, +B](val value : Option[B], val children : SortedMap[A, TrieMap[A, B]]) extends AbstractMap[List[A], B]
  with Map[List[A], B]
  with MapLike[List[A], B, TrieMap[A, B]] {
  override def size = value.size + children.valuesIterator.map(_.size).sum
  override def empty = TrieMap.empty[A, B]
  override def + [B1 >: B] (kv : (List[A], B1)) : TrieMap[A, B1] =
    kv._1 match {
      case Nil => new TrieMap(Some(kv._2), children)
      case a::as => 
        val t = children.get(a) match {
          case None => new TrieMap[A, B](None, SortedMap.empty)
          case Some(t) => t
        }
        new TrieMap(value, children+((a, t+((as, kv._2)))))
    }
  override def -(k : List[A]) : TrieMap[A, B] = k match {
    case Nil => new TrieMap(None, children)
    case a::as => children.get(a) match {
      case None => this
      case Some(t) => new TrieMap(value, children+((a, t-as)))
    }
  }
  override def get(k : List[A]) : Option[B] = k match {
    case Nil => value
    case a::as => children.get(a) match {
      case None => None
      case Some(t) => t.get(as)
    }
  }
  override def iterator : Iterator[(List[A], B)] = (for (v <- value.iterator) yield (Nil, v)) ++ 
    (for (p <- children.iterator; q <- p._2.iterator) yield (p._1::q._1, q._2)) 
  
  override def mapValues[C](f : B => C) : TrieMap[A, C] = 
    new TrieMap(value.map(f), children.mapValues(t => t.mapValues(f)))
  
  def unionWith[B1 >: B](that : TrieMap[A, B1], f : (B1, B1) => B1) : TrieMap[A, B1] = {
    val value1 = (value, that.value) match {
      case (None, v) => v
      case (Some(x), None) => Some(x)
      case (Some(x), Some(y)) => Some(f(x, y))
    }
    return new TrieMap(value1, children.unionWith[TrieMap[A,B1]](that.children, (a, b) => a.unionWith(b, f)))
  }
}

object TrieMap {
  type Coll = TrieMap[_, _]
  def empty[A : Ordering, B] = new TrieMap[A, B](Option.empty, SortedMap.empty)
  def apply[A : Ordering, B](value : Option[B], children : SortedMap[A, TrieMap[A, B]]) = new TrieMap(value, children)
  def apply[A : Ordering, B](elems : (List[A], B)*) = (newBuilder[A, B] ++= elems).result()
  def newBuilder[A : Ordering, B] = new MapBuilder[List[A], B, TrieMap[A, B]](empty[A, B])
  
  class TrieMapCanBuildFrom[A : Ordering, B] extends CanBuildFrom[Coll, (List[A], B), TrieMap[A, B]] {
    def apply(from: Coll) = newBuilder[A, B]
    def apply() = newBuilder
  }
  
  implicit class SortedMapWithUnionWith[A : Ordering, +B](map : SortedMap[A, B]) {
    def unionWith[B1 >: B](that : SortedMap[A, B1], f : (B1, B1) => B1) : SortedMap[A, B1] = {
      import Stream.{Empty, #::}
      def h(as : Stream[(A, B1)], bs : Stream[(A, B1)]) : Stream[(A, B1)] = (as, bs) match {
        case (Empty, bs) => bs
        case (as, Empty) => as
        case ((ak, a) #:: as, (bk, b) #:: bs) =>
          if (ak == bk) (ak, f(a, b)) #:: h(as, bs)
          else if (implicitly[Ordering[A]].lt(ak, bk)) (ak, a) #:: h(as, (bk, b) #:: bs)
          else (bk, b) #:: h((ak, a) #:: as, bs)
      }
      SortedMap(h(map.toStream, that.toStream):_*)
    }
  }
}

