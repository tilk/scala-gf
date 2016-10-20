package org.tilk.gf

import scala.collection.immutable.{IntMap, SortedMap}

object ParseState {
  type Continuation = TrieMap[Token, Set[Active]]
  def apply(pgf : PGF, language : CId, tp : Type) : ParseState = {
    import TrieMap.SortedMapWithUnionWith
    def ftok(a : SortedMap[Token, Continuation], b : SortedMap[Token, Continuation]) = 
      a.unionWith(b, (ta, tb) => ta.unionWith(tb, _ union _))
    val cnc = pgf.getConcrComplete(language).get
    val (acc, items) = cnc.cnccats.get(tp.start) match {
      case Some(CncCat(s, e, lbls)) => 
        val keys = for {
          cat <- s to e
          lbl <- 0 to lbls.length-1
        } yield ActiveKey(cat, lbl)
        keys.foldLeft((SortedMap.empty[Token, Continuation], List[Active]()))((p, key) => 
          predict(ftok, cnc, cnc.pproductions, key, key, 0, p))
      case None => (SortedMap.empty, Nil)
    }
    val chart = Chart(Chart.emptyActive, Nil, Map.empty, cnc.pproductions, cnc.totalCats, 0)
    val cont = TrieMap(Some(items.toSet), acc)
    ParseState(pgf.abstr, cnc, chart, cont)
  }
  private def predict[A](ftok : (SortedMap[Token, Continuation], A) => A, cnc : Concr, forest : IntMap[Set[Production]], 
      key0 : ActiveKey, key : ActiveKey, k : Int, ai : (A, List[Active])) : (A, List[Active]) = {
    def foldProd(p : Production, ai : (A, List[Active])) = p match {
      case PCoerce(fid) => predict(ftok, cnc, forest, key0, ActiveKey(fid, key.lbl), k, ai)
      case PApply(funid, args) => (ai._1, Active(k, 0, funid, cnc.rhs(funid, key.lbl), args, key0)::ai._2)
      case PConst(_, _, _) => ai
    }
    def toItems(key : ActiveKey, k : Int, funids : Set[FId]) = 
      funids.toStream.map { funid => Active(k, 1, funid, cnc.rhs(funid, key.lbl), Nil, key) }.toSet
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
  def process[A](flit : FId => Option[(CId, Expr, List[Token])], ftok : (SortedMap[Token, Continuation], A) => A, 
      cnc : Concr, items : List[Active], ac : (A, Chart)) : (A, Chart) = items match {
    case Nil => ac
    case item :: items =>
      val (acc, chart) = ac
      val lin = cnc.sequences(item.seqid)
      def ftok_(toks : List[Token], item : Active, cnt : A) : A = toks match {
        case Nil => ftok(SortedMap.empty, cnt)
        case tok::toks => ftok(SortedMap((tok, TrieMap((toks, Set(item))))), cnt)
      }
      if (lin.indices.contains(item.ppos)) {
        val xsym = lin(item.ppos)
        xsym.toToken match {
          case Some(tok) =>
            val acc1 = ftok_(List(tok), item.copy(ppos = item.ppos+1), acc)
            process(flit, ftok, cnc, items, (acc1, chart))
          case None => xsym match {
            case SymNE => process(flit, ftok, cnc, items, ac)
            case SymSoftBind => process(flit, ftok, cnc, (item.copy(ppos = item.ppos+1)::items), ac)
            case SymSoftSpace => process(flit, ftok, cnc, (item.copy(ppos = item.ppos+1)::items), ac)
            case SymKP(syms, vars) =>
              val acc1 = (syms::vars.map(_._1)).foldLeft(acc) { (acc, syms) => 
                ftok_(syms.flatMap { sym => sym.toToken.toList }, item.copy(ppos = item.ppos + 1), acc)
              }
              process(flit, ftok, cnc, items, (acc1, chart))
            case SymCat(d, r) => 
              val PArg(hypos, fid) = item.args(d)
              val key = ActiveKey(fid, r)
              lazy val items2 = chart.passive.get(key.makePassive(chart.offset)) match {
                case None => items
                case Some(id) => item.copy(ppos = item.ppos + 1, args = item.args.updated(d, item.args(d).copy(fid = id)))::items
              }
              def uu(forest : IntMap[Set[Production]], fids : (FId, FId)) = cnc.lindefs.get(fids._2) match {
                case None => forest
                case Some(funs) => funs.foldLeft(forest) { (forest, funid) =>
                  forest.updateWith(fids._2, Set(PApply(funid, List(PArg(Nil, fids._1)))), _ union _)
                }
              }
              lazy val parent_sc = (chart.active::chart.actives)(chart.offset - item.j).get(item.key).map(_._2).getOrElse(IntMap.empty)
              lazy val new_sc = hypos.foldLeft(parent_sc)(uu)
              lazy val (acc1, items4) = predict(ftok, cnc, new_sc.unionWith(chart.forest, (_, a, b) => a union b), 
                  key, key, chart.offset, (acc, items2))
              chart.active.get(key) match {
                case None => process(flit, ftok, cnc, items4, (acc1, chart.copy(active = chart.active+((key, (Set(item), new_sc))))))
                case Some((set, sc)) => 
                  if (set(item)) process(flit, ftok, cnc, items, ac)
                  else process(flit, ftok, cnc, items2, 
                      (acc, chart.copy(active = chart.active+((key, (set+item, new_sc.unionWith(sc, (_, a, b) => a union b)))))))
              }
/*            case SymLit(d, r) =>
              val PArg(hypos, fid) = item.args(d)
              val key = ActiveKey(fid, r)
              val fid1 = chart.passive.get(key.makePassive(chart.offset)).getOrElse(fid)*/
              
          }
        }
      } else chart.passive.get(item.key.makePassive(item.j)) match {
        case None =>
          val fid = chart.nextId
          val items2 = (chart.active :: chart.actives)(chart.offset - item.j).get(item.key) match {
            case None => items
            case Some((set, sc)) => 
              def f(act : Active, items : List[Active]) = {
                val SymCat(d, _) = cnc.sequences(act.seqid)(act.ppos)
                act.copy(ppos = act.ppos+1, args = act.args.updated(d, act.args(d).copy(fid = fid))) :: items
              }
              set.foldRight(items)(f)
          }
          process(flit, ftok, cnc, items2, 
              (acc, chart.copy(passive = chart.passive + ((item.key.makePassive(item.j), fid)), 
                  forest = chart.forest + ((fid, Set(PApply(item.funid, item.args)))), nextId = chart.nextId + 1)))
        case Some(id) => 
          val items2 = (for (r <- chart.active.range(ActiveKey(id, 0), ActiveKey(id+1, -1)).map(_._1.lbl)) 
            yield Active(chart.offset, 0, item.funid, cnc.rhs(item.funid, r), item.args, ActiveKey(id, r))) ++ items
          val forest1 = chart.forest.updateWith(id, Set(PApply(item.funid, item.args)), _ union _)
          process(flit, ftok, cnc, items2.toList, (acc, chart.copy(forest = forest1)))
      }
  }
}

final case class ParseInput(
    token : SortedMap[Token, ParseState.Continuation] => Option[ParseState.Continuation], 
    literal : FId => Option[(CId, Expr, List[Token])]
)

final case class ErrorState(abstr : Abstr, concr : Concr, chart : Chart)

final case class ParseState(abstr : Abstr, concr : Concr, chart : Chart, cont : ParseState.Continuation) {
  def next(input : ParseInput) : Either[ErrorState, ParseState] = {
    val agenda = cont.value.map(_.toList).getOrElse(List())
    val cnt = input.token(cont.children).getOrElse(TrieMap.empty)
    def ftok(choices : SortedMap[Token, ParseState.Continuation], cnt : ParseState.Continuation) = input.token(choices) match {
      case Some(cnt1) => cnt1.unionWith(cnt, _ union _)
      case None => cnt
    }
    val (cnt1, chart1) = ParseState.process(input.literal, ftok, concr, agenda, (cnt, chart))
    val chart2 = chart1.copy(active = Chart.emptyActive, actives = chart1.active :: chart1.actives, 
        passive = Chart.emptyPassive, offset = chart1.offset + 1)
    if (cnt1.isEmpty) Left(ErrorState(abstr, concr, chart2))
    else Right(ParseState(abstr, concr, chart2, cnt1))
  }
}

final case class Active(val j : Int, val ppos : DotPos, val funid : FunId, val seqid : SeqId, val args : List[PArg], val key : ActiveKey)

final case class ActiveKey(val fid : FId, val lbl : LIndex) {
  def makePassive(j : Int) = PassiveKey(fid, lbl, j)
}

object ActiveKey {
  implicit object ActiveKeyOrdering extends Ordering[ActiveKey] {
    override def compare(a : ActiveKey, b: ActiveKey) : Int = {
      val c = a.fid compare b.fid
      if (c != 0) c else a.lbl compare b.lbl
    }
  }
}

final case class PassiveKey(val fid : FId, val lbl : LIndex, val j : Int)

object Chart {
  type ActiveChart = SortedMap[ActiveKey, (Set[Active], IntMap[Set[Production]])]
  type PassiveChart = Map[PassiveKey, FId]
  val emptyActive : ActiveChart = SortedMap.empty
  val emptyPassive : PassiveChart = Map.empty
}

final case class Chart(
    val active : Chart.ActiveChart,
    val actives : List[Chart.ActiveChart],
    val passive : Chart.PassiveChart,
    val forest : IntMap[Set[Production]],
    val nextId : FId,
    val offset : Int
)