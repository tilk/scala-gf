package org.tilk.gf

final case class Abstr(
    aflags : Map[CId, Literal],
    funs : Map[CId, (Type, Int, Option[(List[Equation], List[List[Instr]])], Double)],
    cats : Map[CId, (List[Hypo], List[(Double, CId)], Double)]
)

final class Concr(
    cflags : Map[CId, Literal],
    printnames : Map[CId, String],
    cncfun : Array[CncFun],
    lindefs : Map[Int, List[FunId]],
    linrefs : Map[Int, List[FunId]],
    sequences : Array[Array[Symbol]],
    productions : Map[Int, Set[Production]],
    pproductions : Map[Int, Set[Production]],
    lproductions : Map[CId, Map[Int, Set[Production]]],
    cnccats : Map[CId, CncCat],
    lexicon : Map[Int, Map[Int, TrieMap[Token, Set[Int]]]],
    totalCats: FId
)

final case class CncCat(a : FId, b : FId, c : Array[String])
final case class CncFun(a : CId, b : Array[SeqId]) 

abstract sealed class Production
final case class PApply(id : FunId, args : List[PArg]) extends Production
final case class PCoerce(id : FId) extends Production
final case class PConst(id : CId, expr : Expr, tokens : List[Token]) extends Production

final case class PArg(a : List[(FId, FId)], b : FId)

class PGF(gflags : Map[String, Literal], absname : CId, abstr : Abstr, concr : Map[CId, Concr]) {
  
}

