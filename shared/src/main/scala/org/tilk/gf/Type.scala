package org.tilk.gf

final case class Type(hypo : List[Hypo], id : CId, exprs : List[Expr])

final case class Hypo(bindtype : BindType, id : CId, tp : Type)
