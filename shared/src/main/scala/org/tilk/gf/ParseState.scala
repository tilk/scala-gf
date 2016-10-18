package org.tilk.gf

import scala.collection.immutable.{IntMap, SortedMap}

object ParseState {
  type Continuation = TrieMap[Token, Set[Active]]
  def apply(pgf : PGF, language : CId, tp : Type) : ParseState = {
    import TrieMap.SortedMapWithUnionWith
    def ftok(a : SortedMap[Token, TrieMap[Token, Set[Active]]], b : SortedMap[Token, TrieMap[Token, Set[Active]]]) = 
      a.unionWith(b, (ta, tb) => ta.unionWith(tb, _ union _))
    val cnc = pgf.getConcrComplete(language).get
    val (acc, items) = cnc.cnccats.get(tp.start) match {
      case Some(CncCat(s, e, lbls)) => 
        val keys = for {
          cat <- s to e
          lbl <- 0 to lbls.length-1
        } yield ActiveKey(cat, lbl)
        keys.foldLeft((SortedMap.empty[Token, TrieMap[Token, Set[Active]]], List[Active]()))((p, key) => 
          predict(ftok, cnc, cnc.pproductions, key, key, 0, p))
      case None => (SortedMap.empty, Nil)
    }
    val chart = Chart(Chart.emptyActive, Nil, Map.empty, cnc.pproductions, cnc.totalCats, 0)
    val cont = TrieMap(Some(items.toSet), acc)
    ParseState(pgf.abstr, cnc, chart, cont)
  }
  def predict[A](ftok : (SortedMap[Token, TrieMap[Token, Set[Active]]], A) => A, cnc : Concr, forest : IntMap[Set[Production]], 
      key0 : ActiveKey, key : ActiveKey, k : Int, ai : (A, List[Active])) : (A, List[Active]) = {
    def rhs(fid : FId, lbl : LIndex) = cnc.cncfuns(fid).lins(lbl)
    def foldProd(p : Production, ai : (A, List[Active])) = p match {
      case PCoerce(fid) => predict(ftok, cnc, forest, key0, ActiveKey(fid, key.lbl), k, ai)
      case PApply(funid, args) => (ai._1, Active(k, 0, funid, rhs(funid, key.lbl), args, key0)::ai._2)
      case PConst(_, _, _) => ai
    }
    def toItems(key : ActiveKey, k : Int, funids : Set[FId]) = 
      funids.toStream.map { funid => Active(k, 1, funid, rhs(funid, key.lbl), Nil, key) }.toSet
    val ai1 = forest.get(key.fid) match {
      case None => ai
      case Some(set) => set.foldRight(ai)(foldProd)
    }
    val ai2 = cnc.lexicon.get(key.fid).flatMap(m => m.get(key.lbl)) match {
      case None => ai1
      case Some(tmap) => 
        val tmap1 = tmap.mapValues { x => toItems(key0, k, x) }
        (ftok(tmap1.children, ai1._1), tmap1.value.map(_.toList).getOrElse(Nil) ++ ai1._2)
    }
    ai2
  }
}

final case class ParseState(abstr : Abstr, concr : Concr, chart : Chart, cont : ParseState.Continuation) {
 
}

final case class Active(a : Int, b : DotPos, c : FunId, d : SeqId, e : List[PArg], f : ActiveKey)

final case class ActiveKey(val fid : FId, val lbl : LIndex)

object ActiveKey {
  implicit object ActiveKeyOrdering extends Ordering[ActiveKey] {
    override def compare(a : ActiveKey, b: ActiveKey) : Int = {
      val c = a.fid compare b.fid
      if (c != 0) c else a.lbl compare b.lbl
    }
  }
}

final case class PassiveKey(a : FId, b : LIndex, c : Int)

object Chart {
  type ActiveChart = SortedMap[ActiveKey, (Set[Active], IntMap[Set[Production]])]
  type PassiveChart = Map[PassiveKey, FId]
  val emptyActive : ActiveChart = SortedMap.empty
}

final case class Chart(
    val active : Chart.ActiveChart,
    val actives : List[Chart.ActiveChart],
    val passive : Chart.PassiveChart,
    val forest : IntMap[Set[Production]],
    val nextId : FId,
    val offset : Int
)

