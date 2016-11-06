package org.tilk.gf

import scala.collection.immutable.IntMap

final case class Abstr(
    val aflags : Map[CId, Literal],
    val funs : Map[CId, (Type, Int, Option[(List[Equation], List[List[Instr]])], Double)],
    val cats : Map[CId, (List[Hypo], List[(Double, CId)], Double)]
)

final case class Concr(
    val cflags : Map[CId, Literal],
    val printnames : Map[CId, String],
    val cncfuns : Vector[CncFun],
    val lindefs : IntMap[List[FunId]],
    val linrefs : IntMap[List[FunId]],
    val sequences : Vector[Vector[Symbol]],
    val productions : IntMap[Set[Production]],
    val pproductions : IntMap[Set[Production]],
    val lproductions : Map[CId, IntMap[Set[Production]]],
    val cnccats : Map[CId, CncCat],
    val lexicon : IntMap[IntMap[TrieMap[Token, Set[Int]]]],
    val totalCats: FId
) {
  def rhs(fid : FId, lbl : LIndex) = cncfuns(fid).lins(lbl)
}

final case class CncCat(a : FId, b : FId, c : Vector[String])
final case class CncFun(a : CId, lins : Vector[SeqId]) 

abstract sealed class Production
final case class PApply(id : FunId, args : List[PArg]) extends Production
final case class PCoerce(id : FId) extends Production
final case class PConst(id : CId, expr : Expr, tokens : List[Token]) extends Production

final case class PArg(val hypos : List[(FId, FId)], val fid : FId)

abstract sealed class Symbol {
  val toToken : Option[Token] = None
  def inc(k : Int) = this
}
final case class SymCat(d : Int, r : LIndex) extends Symbol { override def inc(k : Int) = SymCat(k+d, r) }
final case class SymLit(d : Int, r : LIndex) extends Symbol { override def inc(k : Int) = SymLit(k+d, r) }
final case class SymVar(d : Int, r : Int) extends Symbol { override def inc(k : Int) = SymVar(k+d, r) }
final case class SymKS(token : Token) extends Symbol { override val toToken : Option[Token] = Some(token) }
final case class SymKP(syms : List[Symbol], vars : List[(List[Symbol], List[String])]) extends Symbol
final case object SymBind extends Symbol { override val toToken : Option[Token] = Some("&+") }
final case object SymNE extends Symbol
final case object SymSoftBind extends Symbol
final case object SymSoftSpace extends Symbol
final case object SymCapit extends Symbol { override val toToken : Option[Token] = Some("&|") }
final case object SymAllCapit extends Symbol { override val toToken : Option[Token] = Some("&|") }

case class PGF(
    val gflags : Map[String, Literal], 
    val absname : CId, 
    val abstr : Abstr, 
    val concr : Map[CId, Concr]
) {

  def getConcrComplete(id : CId) : Option[Concr] = 
    concr.get(id).orElse(concr.get(CId(absname.value + id.value)))
  def parse(lang : CId, typ : Type, dp : Option[Int] = Some(4), s : String) : (ParseOutput, BracketedString) = 
    ParseState.parse(this, lang, typ, dp, s.split(' ').toList)
  def linearize(lang : CId, e : Expr) = bracketedLinearize(lang, e).flatMap(_.flatten).mkString(" ")
  def bracketedLinearize(lang : CId, e : Expr) = {
    val cnc = concr(lang)
    new Linearize(this, cnc).linTree(e).map(l => BracketedToken.untoken(None, l.firstLin(cnc))._2).head
  } 
}

