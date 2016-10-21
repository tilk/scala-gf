package org.tilk.gf

abstract sealed class TcError
case class UnknownCat(cid : CId) extends TcError
case class UnknownFun(cid : CId) extends TcError
case class WrongCatArgs(cids : List[CId], tp : Type, cid : CId, expected : Int, given : Int) extends TcError
case class TypeMismatch(cids : List[CId], e : Expr, t1 : Type, t2 : Type) extends TcError
case class NotFunType(cids : List[CId], e : Expr, tp : Type) extends TcError
case class CannotInferType(cids : List[CId], e : Expr) extends TcError
case class UnresolvedMetaVars(cids : List[CId], e : Expr, metas : List[MetaId]) extends TcError
case class UnexpectedImplArg(cids: List[CId], e : Expr) extends TcError
case class UnsolvableGoal(cids : List[CId], meta : MetaId, tp : Type) extends TcError