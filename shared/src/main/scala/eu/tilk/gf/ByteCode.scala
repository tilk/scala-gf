package eu.tilk.gf

abstract sealed class Literal
case class LStr(val value : String) extends Literal
case class LInt(val value : Int) extends Literal
case class LFlt(val value : Double) extends Literal

abstract sealed class Instr
case class ICheckArgs(i : Int) extends Instr
case class ICase(id : CId) extends Instr
case class ICaseLit(lit : Literal, label : CodeLabel) extends Instr
case class ISave(i : Int) extends Instr
case class IAlloc(i : Int) extends Instr
case class IPutConstr(id : CId) extends Instr
case class IPutClosure(label : CodeLabel) extends Instr
case class IPutLiteral(lit : Literal) extends Instr
case class ISet(v : IVal) extends Instr
case object ISetPad extends Instr
case class IPush(v : IVal) extends Instr
case class ITuck(v : IVal, i : Int) extends Instr
case class IEval(v : IVal, ti : TailInfo) extends Instr
case class IDrop(i : Int) extends Instr
case class IJump(label : CodeLabel) extends Instr
case object IFail extends Instr
case class IPushAccum(lit : Literal) extends Instr
case object IPopAccum extends Instr
case object IAdd extends Instr

abstract sealed class IVal
case class IVHeap(i : Int) extends IVal
case class IVArgVar(i : Int) extends IVal
case class IVFreeVar(i : Int) extends IVal
case class IVGlobal(id : CId) extends IVal

abstract sealed class TailInfo
case object RecCall extends TailInfo
case object TailCall extends TailInfo
case object UpdateCall extends TailInfo
