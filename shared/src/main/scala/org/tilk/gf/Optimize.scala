package org.tilk.gf

import scala.collection.immutable.{IntMap, SortedMap}

object Optimize {
  def filterProductions(prods0 : IntMap[Set[Production]], hoc0 : Set[Int], prods : IntMap[Set[Production]]) : IntMap[Set[Production]] = {
    def isLive(fid : FId) = isPredefFId(fid) || prods0.get(fid).isDefined || hoc0(fid)
    def filterRule(p : Production) = p match {
      case PApply(funid, args) => args.forall(parg => isLive(parg.fid))
      case PCoerce(fid) => isLive(fid)
      case _ => true
    }
    def accumHOC(hoc : Set[Int], p : Production) = p match {
      case PApply(funid, args) => args.foldLeft(hoc){ (hoc, parg) =>
        parg.hypos.foldLeft(hoc){ (hoc, hypo) =>
          hoc + hypo._2
        }
      } 
      case _ => hoc
    }
    val (prods1, hoc1) = prods.foldLeft((IntMap[Set[Production]](), Set[Int]())) { (p1, p2) => 
      val (fid, set) = p2
      val set1 = set.filter(filterRule)
      if (set1.isEmpty) p1 
      else {
        val (prods, hoc) = p1
        val hoc1 = set1.foldLeft(hoc)(accumHOC)
        (prods+((fid, set1)), hoc1)
      }
    }
    if (prods0 == prods1) prods0
    else filterProductions(prods1, hoc1, prods)
  }
  def splitLexicalRules(cnc : Concr, p_prods : IntMap[Set[Production]]) = 
    p_prods.foldLeft((IntMap[IntMap[TrieMap[Token, Set[FunId]]]](), IntMap[Set[Production]]())) { (p1, p2) =>
    def isLexical(p : Production) = p match {
      case PApply(_, Nil) => true
      case _ => false
    }
    def words(funid : FunId) : IntMap[TrieMap[Token, Set[FunId]]] = {
      val CncFun(_, lins) = cnc.cncfuns(funid)
      def wf(ts : List[Token]) = (ts, Set(funid))
      def seq2prefix(syms : List[Symbol]) : TrieMap[Token, Set[FunId]] = syms match {
        case Nil => TrieMap(wf(Nil))
        case SymKS(t)::_ => TrieMap(wf(List(t)))
        case SymKP(syms0, alts)::syms => 
          (seq2prefix(syms0 ++ syms)::(for ((syms1, ps) <- alts) yield seq2prefix(syms1 ++ syms))).fold(TrieMap.empty)((a, b) => a.unionWith(b, _ union _))
        case SymNE::_ => TrieMap.empty
        case SymBind::_ => TrieMap(wf(List("&+")))
        case SymSoftBind::_ => TrieMap(wf(Nil))
        case SymSoftSpace::_ => TrieMap(wf(Nil))
        case SymCapit::_ => TrieMap(wf(List("&|")))
        case SymAllCapit::_ => TrieMap(wf(List("&|")))
      }
      val vect = for ((seqid, lbl) <- lins.zipWithIndex) yield (lbl, seq2prefix(cnc.sequences(seqid).toList))
      IntMap(vect:_*)
    }
    val (fid, set) = p2
    val (lex, syn) = p1
    val (lex0, syn0) = set.partition(isLexical)
    val lex1 = if (lex0.isEmpty) lex else {
      val mp = (for (PApply(funid, Nil) <- lex0) yield words(funid)).fold(IntMap.empty)((a, b) => a.unionWith(b, (_, c, d) => c.unionWith(d, _ union _))) 
      lex+((fid, mp))
    }
    val syn1 = if (syn0.isEmpty) syn else syn+((fid, syn0))
    (lex1, syn1)
  }
  def linIndex(cnc : Concr, productions : IntMap[Set[Production]]) : Map[CId, IntMap[Set[Production]]] = {
    import TrieMap.SortedMapWithUnionWith
    def getFunctions(p : Production) : List[CId] = p match {
      case PApply(funid, args) => List(cnc.cncfuns(funid).fun)
      case PCoerce(fid) => productions.get(fid) match {
        case None => Nil
        case Some(prods) => for (prod <- prods.toList; fun <- getFunctions(prod)) yield fun
      }
    }
    val it = for ((res, prods) <- productions; prod <- prods; fun <- getFunctions(prod)) yield SortedMap((fun, IntMap((res, Set(prod)))))
    it.foldLeft(SortedMap[CId, IntMap[Set[Production]]]())((a, b) => a.unionWith(b, (c,d) => c.unionWith(d, (_,e,f) => e union f)))
  }
}