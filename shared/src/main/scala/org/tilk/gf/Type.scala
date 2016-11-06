package org.tilk.gf

final case class Type(val hyps : List[Hypo], val start : CId, val exprs : List[Expr]) {
  def contextLength = hyps.length
  def catSkeleton = (for (h <- hyps) yield h.tp.start, start)
  def typeSkeleton = (for (h <- hyps; val ty = h.tp) yield (ty.contextLength, ty.start), start)
}

final case class Hypo(bindtype : BindType, id : CId, tp : Type)
