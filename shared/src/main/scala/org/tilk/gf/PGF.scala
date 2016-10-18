package org.tilk.gf

final case class Abstr(
    val aflags : Map[CId, Literal],
    val funs : Map[CId, (Type, Int, Option[(List[Equation], List[List[Instr]])], Double)],
    val cats : Map[CId, (List[Hypo], List[(Double, CId)], Double)]
)

final case class Concr(
    val cflags : Map[CId, Literal],
    val printnames : Map[CId, String],
    val cncfun : Vector[CncFun],
    val lindefs : Map[Int, List[FunId]],
    val linrefs : Map[Int, List[FunId]],
    val sequences : Vector[Vector[Symbol]],
    val productions : Map[Int, Set[Production]],
    val pproductions : Map[Int, Set[Production]],
    val lproductions : Map[CId, Map[Int, Set[Production]]],
    val cnccats : Map[CId, CncCat],
    val lexicon : Map[Int, Map[Int, TrieMap[Token, Set[Int]]]],
    val totalCats: FId
)

final case class CncCat(a : FId, b : FId, c : Vector[String])
final case class CncFun(a : CId, b : Vector[SeqId]) 

abstract sealed class Production
final case class PApply(id : FunId, args : List[PArg]) extends Production
final case class PCoerce(id : FId) extends Production
final case class PConst(id : CId, expr : Expr, tokens : List[Token]) extends Production

final case class PArg(a : List[(FId, FId)], b : FId)

abstract sealed class Symbol
final case class SymCat(a : Int, b : LIndex) extends Symbol
final case class SymLit(a : Int, b : LIndex) extends Symbol
final case class SymVar(a : Int, b : Int) extends Symbol
final case class SymKS(token : Token) extends Symbol
final case class SymKP(a : List[Symbol], b : List[(List[Symbol], List[String])]) extends Symbol
final case object SymBind extends Symbol
final case object SymNE extends Symbol
final case object SymSoftBind extends Symbol
final case object SymSoftSpace extends Symbol
final case object SymCapit extends Symbol
final case object SymAllCapit extends Symbol

case class PGF(
    val gflags : Map[String, Literal], 
    val absname : CId, 
    val abstr : Abstr, 
    val concr : Map[CId, Concr]
) 

