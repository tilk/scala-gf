package org.tilk.gf

abstract sealed class BindType
case object Implicit extends BindType
case object Explicit extends BindType

abstract sealed class Expr
case class EAbs(val bindtype : BindType, val id : CId, val expr : Expr) extends Expr
case class EApp(val fun : Expr, val app : Expr) extends Expr
case class ELit(val lit : Literal) extends Expr
case class EMeta(val id : MetaId) extends Expr
case class EFun(val id : CId) extends Expr
case class EVar(val idx : Int) extends Expr
case class ETyped(val expr : Expr, val tp : Type) extends Expr
case class EImplArg(val expr : Expr) extends Expr

abstract sealed class Patt
case class PApp(val id : CId, val pats : List[Patt]) extends Patt
case class PLit(val lit : Literal) extends Patt
case class PVar(val id : CId) extends Patt
case class PAs(val id : CId, val patt : Patt) extends Patt
case object PWild extends Patt
case class PImplArg(val patt : Patt) extends Patt
case class PTilde(val expr : Expr) extends Patt

final case class Equation(pats : List[Patt], expr : Expr)