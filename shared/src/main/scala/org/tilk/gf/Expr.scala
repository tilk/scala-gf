package org.tilk.gf

abstract sealed class BindType
case object Implicit extends BindType
case object Explicit extends BindType

final case class Sig(val funs : Map[CId, (Type, Int, Option[(List[Equation], List[List[Instr]])], Double)], val metas : Int => Option[Expr])

abstract sealed class Expr {
  def eval(sig : Sig, env : Env) : Value = this match {
    case EVar(i) => env(i)
    case EFun(f) => sig.funs.get(f) match {
      case Some((_,a,meqs,_)) => meqs match {
        case Some((eqs, _)) =>
          if (a == 0) eqs match {
            case Equation(Nil, e) :: _ => e.eval(sig, Nil)
            case _ => VConst(f, Nil)
          }
          else VApp(f, Nil)
        case None => VApp(f, Nil) 
      }
      case None => throw new Exception("Unknown function")
    }
    case EApp(e1, e2) => e1.apply(sig, env, List(e2.eval(sig, env)))
    case a@EAbs(b, x, e) => VClosure(env, a)
    case EMeta(i) => sig.metas(i) match {
      case Some(e) => e.eval(sig, env)
      case None => VMeta(i, env, Nil)
    }
    case ELit(l) => VLit(l)
    case ETyped(e, _) => e.eval(sig, env)
    case EImplArg(e) => VImplArg(e.eval(sig, env))
  }
  def apply(sig : Sig, env : Env, vals : List[Value]) : Value = if (vals.isEmpty) eval(sig, env) else this match {
    case EVar(i) => env(i).apply(sig, vals)
    case EFun(f) => sig.funs.get(f) match {
      case Some((_,a,meqs,_)) => meqs match {
        case Some((eqs, _)) =>
          if (a <= vals.length) Equation.matching(sig, f, eqs, vals)
          else VApp(f, vals) 
        case None => VApp(f, vals)
      }
      case None => throw new Exception("Unknown function")
    }
    case EApp(e1, e2) => e1.apply(sig, env, e2.eval(sig, env) :: vals)
    case EAbs(b, x, e) => (b, vals.head) match {
      case (Implicit, VImplArg(v)) => e.apply(sig, v::env, vals.tail)
      case (Explicit, v) => e.apply(sig, v::env, vals.tail)
      case (Implicit, _) => throw new Exception()
    }
    case EMeta(i) => sig.metas(i) match {
      case Some(e) => e.apply(sig, env, vals)
      case None => VMeta(i, env, vals)
    }
    case ELit(l) => throw new Exception("literal of function type")
    case ETyped(e, _) => e.apply(sig, env, vals)
    case EImplArg(_) => throw new Exception("implicit argument in function position")
  }
}
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

object Equation {
  def matching(sig : Sig, f : CId, eqs : List[Equation], as0 : List[Value]) : Value = eqs match {
    case Nil => VConst(f, as0)
    case Equation(ps, res) :: eqs => 
      def tryMatches(eqs : List[Equation], ps : List[Patt], as : List[Value], res : Expr, env : Env) : Value = (ps, as) match {
        case (Nil, as) => res.apply(sig, env, as)
        case (p :: ps, a :: as) => 
          def tryMatch(p : Patt, a : Value, env : Env) : Value = (p, a) match {
            case (PVar(x), v) => tryMatches(eqs, ps, as, res, v :: env)
            case (PAs(x, p), v) => tryMatch(p, v, v :: env)
            case (PWild, _) => tryMatches(eqs, ps, as, res, env)
            case (p, VMeta(i, envi, vs)) => VSusp(i, envi, vs, v => tryMatch(p, v, env))
            case (p, VGen(i, vs)) => VConst(f, as0)
            case (p, VSusp(i, envi, vs, k)) => VSusp(i, envi, vs, v => tryMatch(p, k(v), env))
            case (p, VConst(_, _)) => VConst(f, as0)
            case (PApp(f1, ps1), VApp(f2, vs2)) if f1 == f2 => tryMatches(eqs, ps1++ps, vs2++as, res, env)
            case (PLit(l1), VLit(l2)) if l1 == l2 => tryMatches(eqs, ps, as, res, env)
            case (PImplArg(p), VImplArg(v)) => tryMatch(p, v, env)
            case (PTilde(_), _) => tryMatches(eqs, ps, as, res, env)
            case (_, _) => matching(sig, f, eqs, as0) 
            
          }
          tryMatch(p, a, env)
        case (_ :: _, Nil) => throw new Exception()
      }
      tryMatches(eqs, ps, as0, res, Nil)
  }
}

abstract sealed class Value {
  def apply(sig : Sig, vs : List[Value]) : Value = if (vs.isEmpty) this else this match {
    case VApp(f, vs0) => EFun(f).apply(sig, Nil, vs0 ++ vs)
    case VLit(_) => throw new Exception("literal of function type")
    case VMeta(i, env, vs0) => VMeta(i, env, vs0 ++ vs)
    case VGen(i, vs0) => VGen(i, vs0 ++ vs)
    case VSusp(i, env, vs0, k) => VSusp(i, env, vs0, v => k(v).apply(sig, vs))
    case VConst(f, vs0) => VConst(f, vs0 ++ vs)
    case VClosure(env, EAbs(b, x, e)) => (b, vs.head) match {
      case (Implicit, VImplArg(v)) => e.apply(sig, v::env, vs.tail)
      case (Explicit, v) => e.apply(sig, v::env, vs.tail)
      case (Implicit, _) => throw new Exception()
    }
    case VImplArg(_) => throw new Exception("implicit argument in function position")
  }
  
  def toExpr(sig : Sig, i : Int) : Expr = this match {
    case VApp(f, vs) => vs.map(_.toExpr(sig, i)).foldLeft(EFun(f):Expr)(EApp)
    case VGen(j, vs) => vs.map(_.toExpr(sig, i)).foldLeft(EVar(i-j-1):Expr)(EApp)
    case VMeta(j, env, vs) => sig.metas(j) match {
      case Some(e) => e.apply(sig, env, vs).toExpr(sig, i)
      case None => vs.map(_.toExpr(sig, i)).foldLeft(EMeta(j):Expr)(EApp)
    }
    case VSusp(j, env, vs, k) => k(VGen(j, vs)).toExpr(sig, i)
    case VConst(f, vs) => vs.map(_.toExpr(sig, i)).foldLeft(EFun(f):Expr)(EApp)
    case VClosure(env, EAbs(b, x, e)) => EAbs(b, CId("v" ++ i.toString), e.eval(sig, VGen(i, Nil)::env).toExpr(sig, i+1)) 
    case VLit(l) => ELit(l)
    case VImplArg(v) => EImplArg(v.toExpr(sig,i))
  }
}
case class VApp(val id : CId, val values : List[Value]) extends Value
case class VLit(val lit : Literal) extends Value
case class VMeta(val m : MetaId, val env : Env, val values : List[Value]) extends Value
case class VSusp(val m : MetaId, val env : Env, val values : List[Value], val f : Value => Value) extends Value
case class VGen(val n : Int, val values : List[Value]) extends Value
case class VConst(val id : CId, val values : List[Value]) extends Value
case class VClosure(val env : Env, val expr : EAbs) extends Value
case class VImplArg(val value : Value) extends Value
