package org.tilk.gf

final case class Type(val hypo : List[Hypo], val start : CId, val exprs : List[Expr])

final case class Hypo(bindtype : BindType, id : CId, tp : Type)
