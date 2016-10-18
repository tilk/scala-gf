package org.tilk.gf

import scala.collection.generic._
import scala.collection.mutable.MapBuilder
import scala.collection.immutable.{AbstractMap, Map, MapLike}

final class TrieMap[A, +B](value : Option[B], children : Map[A, TrieMap[A, B]]) extends AbstractMap[List[A], B]
  with Map[List[A], B]
  with MapLike[List[A], B, TrieMap[A, B]] {
  override def size = value.size + children.valuesIterator.map(_.size).sum
  override def empty = TrieMap.empty[A, B]
  override def + [B1 >: B] (kv : (List[A], B1)) : TrieMap[A, B1] =
    kv._1 match {
      case Nil => new TrieMap(Some(kv._2), children)
      case a::as => children.get(a) match {
        case None => new TrieMap(value, children+((a, new TrieMap(Some(kv._2), Map.empty))))
        case Some(t) => new TrieMap(value, children+((a, t+((as, kv._2)))))
      }
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
}

object TrieMap {
  type Coll = TrieMap[_, _]
  def empty[A, B] = new TrieMap[A, B](Option.empty, Map.empty)
  def apply[A, B](elems : (List[A], B)*) = (newBuilder[A, B] ++= elems).result()
  def newBuilder[A, B] = new MapBuilder[List[A], B, TrieMap[A, B]](empty[A, B])
  
  class TrieMapCanBuildFrom[A, B] extends CanBuildFrom[Coll, (List[A], B), TrieMap[A, B]] {
    def apply(from: Coll) = newBuilder[A, B]
    def apply() = newBuilder
  }
}

