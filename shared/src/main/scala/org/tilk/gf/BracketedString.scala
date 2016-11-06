package org.tilk.gf

import scalaz._
import Scalaz._

sealed abstract class BracketedString {
  def flatten : List[String] = this match {
    case BSLeaf(w) => List(w)
    case BSBracket(_,_,_,_,_,bss) => bss.flatMap(_.flatten)
  }
  def length : Int = this match {
    case BSLeaf(_) => 1
    case BSBracket(_,_,_,_,_,bss) => bss.map(_.length).sum 
  }
}
case class BSLeaf(token : Token) extends BracketedString
case class BSBracket(id : CId, fid : FId, idx : LIndex, cid2 : CId, exprs : List[Expr], substrings : List[BracketedString]) extends BracketedString

sealed abstract class BracketedToken
case class BTBracket(cid : CId, fid : FId, idx : LIndex, cid2 : CId, exprs : List[Expr], subtokens : List[BracketedToken]) extends BracketedToken
case class BTLeafKS(token : Token) extends BracketedToken
case object BTLeafNE extends BracketedToken
case object BTLeafBind extends BracketedToken
case object BTLeafSoftBind extends BracketedToken
case object BTLeafCapit extends BracketedToken
case class BTLeafKP(subtokens : List[BracketedToken], l : List[(List[BracketedToken], List[String])]) extends BracketedToken

object BracketedToken {
  def untoken(nw : Option[String], bss : List[BracketedToken]) : (Option[String], List[BracketedString]) = {
    def sel(d : List[BracketedToken], vs : List[(List[BracketedToken], List[String])], nw : Option[String]) = nw match {
      case None => d
      case Some(w) => (for ((v, cs) <- vs; if cs.any { x => w startsWith x }) yield v).headOption.getOrElse(d)
    }
    def untokn(nw : Option[String], bt : BracketedToken) : (Option[String], Option[List[BracketedString]]) = bt match {
      case BTBracket(cat, fid, index, fun, es, bss) =>
        val (nw1, bss1) = bss.mapAccumRight(nw, untokn)
        bss1.sequence match {
          case Some(bss) => (nw1, Some(List(BSBracket(cat, fid, index, fun, es, bss.concatenate)))) 
          case None => (None, None)
        }
      case BTLeafKS(t) => if (t.isEmpty) (nw, Some(Nil)) else (Some(t), Some(List(BSLeaf(t))))
      case BTLeafNE => (None, None)
      case BTLeafKP(d, vs) => 
        val (nw1, bss1) = sel(d, vs, nw).mapAccumRight(nw, untokn) 
        bss1.sequence match {
          case Some(bss) => (nw1, Some(bss.concatenate))
          case None => (None, None)
        }
    }
    val (nw1, bss1) = bss.mapAccumRight(nw, untokn)
    bss1.sequence match {
      case Some(bss) => (nw, bss.concatenate)
      case None => (None, Nil)
    }
  }
}

final case class LinTable(cids : List[CId], toks : Vector[List[BracketedToken]])

object LinTable {
  def apply(cnc : Concr, filter : CncType => Boolean, xs : List[CId], funid : FunId, args : List[(CncType, FId, CId, List[Expr], LinTable)]) : LinTable = {
    val CncFun(_, lins) = cnc.cncfuns(funid) 
    LinTable(xs, lins.map(seqid => computeSeq(filter, cnc.sequences(seqid).toList, args)))
  }
  def computeSeq(filter : CncType => Boolean, seq : List[Symbol], args : List[(CncType, FId, CId, List[Expr], LinTable)]) : List[BracketedToken] = {
    def getArg(d : Int, r : LIndex) = {
      val (ct@(cat, fid), _, fun, es, LinTable(_xs, lin)) = args(d)
      val arg_lin = lin(r)
      if (!arg_lin.isEmpty && filter(ct)) List(BTBracket(cat, fid, r, fun, es, arg_lin))
      else arg_lin
    }
    def getVar(d : Int, r : LIndex) = {
      val (_ct, _, fun, es, LinTable(xs, _lin)) = args(d)
      List(BTLeafKS(xs(r).value))
    }
    def compute(s : Symbol) : List[BracketedToken] = s match {
      case SymCat(d, r) => getArg(d, r)
      case SymLit(d, r) => getArg(d, r)
      case SymVar(d, r) => getVar(d, r)
      case SymKS(t) => List(BTLeafKS(t))
      case SymNE => List(BTLeafNE)
      case SymBind => List(BTLeafKS("&+"))
      case SymSoftBind => Nil
      case SymSoftSpace => Nil
      case SymCapit => List(BTLeafKS("&|"))
      case SymAllCapit => List(BTLeafKS("&|"))
      case SymKP(syms, alts) => List(BTLeafKP(syms.flatMap(compute), for ((syms, cs) <- alts) yield (syms.flatMap(compute), cs)))
    }
    seq.flatMap(compute).toList
  }
}