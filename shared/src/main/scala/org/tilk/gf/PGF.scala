package org.tilk.gf

import scala.collection.immutable.IntMap
import scodec.bits.ByteVector
import fastparse.byte.all.Parsed
import scalaz._
import Scalaz._

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
  def update(abstr : Abstr) = {
    val p_prods0 = Optimize.filterProductions(IntMap.empty, Set.empty, productions)
    val (lex, p_prods) = Optimize.splitLexicalRules(this, p_prods0)
    val l_prods = Optimize.linIndex(this, productions)
    this.copy(pproductions = p_prods, lproductions = l_prods, lexicon = lex)
  }
}

final case class CncCat(a : FId, b : FId, c : Vector[String])
final case class CncFun(val fun : CId, val lins : Vector[SeqId]) 

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
    val gflags : Map[CId, Literal], 
    val absname : CId, 
    val abstr : Abstr, 
    val concr : Map[CId, Concr]
) {
  def startCat = List(gflags, abstr.aflags).map(_.get(CId("startcat"))).msuml match {
    case Some(LStr(s)) => CId(s)
    case _ => CId("S")
  }
  def startType = Type(Nil, startCat, Nil)
  def getConcrComplete(id : CId) : Option[Concr] = 
    concr.get(id).orElse(concr.get(CId(absname.value + id.value)))
  def parse(lang : CId, s : String, typ : Type = startType, dp : Option[Int] = Some(4)) : (ParseOutput, BracketedString) = 
    ParseState.parse(this, lang, typ, dp, s.split(' ').toList)
  def linearize(lang : CId, e : Expr) = bracketedLinearize(lang, e).flatMap(_.flatten).mkString(" ")
  def bracketedLinearize(lang : CId, e : Expr) = {
    val cnc = getConcrComplete(lang).get
    new Linearize(this, cnc).linTree(e).map(l => BracketedToken.untoken(None, l.firstLin(cnc))._2).head
  } 
  
  def updateProductionIndices : PGF = this.copy(concr = concr.mapValues(_.update(abstr)))
}

object PGF {
  def apply(data : Array[Byte]) : PGF = apply(ByteVector(data))
  def apply(data : ByteVector) : PGF = parse(data) match {
    case Right(v) => v
    case Left(msg) => throw new Exception(msg)
  }
  def parse(data : Array[Byte]) : Either[String, PGF] = parse(ByteVector(data))
  def parse(data : ByteVector) : Either[String, PGF] = Parser.parsePGF.parse(data) match {
    case Parsed.Success(v, si) => Right(v)
    case p : Parsed.Failure => Left(p.extra.traced.trace)
  }
}
