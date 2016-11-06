package org.tilk.gf

import scala.collection.immutable.IntMap

class Linearize(pgf : PGF, cnc : Concr) {
  def linTree(e : Expr) : List[Linearization] = lin(None, 0, e, Nil, Nil, e, Nil).map(_._2).distinct
  def ss(s : String) = Vector(List(BTLeafKS(s)))
  private def lin(mb_cty : Option[CncType], n_fid : FId, e0 : Expr, 
      ys : List[CId], xs : List[CId], e : Expr, es : List[Expr]) : List[(FId, Linearization)] = e match {
    case EAbs(_, x, e) => lin(mb_cty, n_fid, e0, ys, x::xs, e, es)
    case EApp(e1, e2) => lin(mb_cty, n_fid, e0, ys, xs, e1, e2::es)
    case EImplArg(e) => lin(mb_cty, n_fid, e0, ys, xs, e, es)
    case ETyped(e, _) => lin(mb_cty, n_fid, e0, ys, xs, e, es)
    case EFun(f) => apply(mb_cty, n_fid, e0, ys, xs, f, es)
    case EMeta(i) => df(mb_cty, n_fid, e0, ys, xs, "?"+i)
    case EVar(i) => df(mb_cty, n_fid, e0, ys, xs, (xs++ys:List[CId])(i).value)
    case ELit(l) => l match {
      case LStr(s) => List((n_fid+1, Linearization((cidString, n_fid), fidString, wildCId, List(e0), LinTable(Nil, ss(s)))))
      case LInt(n) => List((n_fid+1, Linearization((cidInt   , n_fid), fidInt,    wildCId, List(e0), LinTable(Nil, ss(n.toString)))))
      case LFlt(f) => List((n_fid+1, Linearization((cidFloat , n_fid), fidFloat,  wildCId, List(e0), LinTable(Nil, ss(f.toString)))))
    }
  }
  private def apply(mb_cty : Option[CncType], n_fid : FId, e0 : Expr, 
      ys : List[CId], xs : List[CId], f : CId, es : List[Expr]) : List[(FId, Linearization)] = {
    def descend(n_fid : FId, fes : List[(CncType, Expr)]) : List[(FId, List[Linearization])] = fes match {
      case Nil => List((n_fid, Nil))
      case (cty, e)::fes => for {
        (n_fid, arg) <- lin(Some(cty), n_fid, e, xs ++ ys, Nil, e, Nil)
        (n_fid, args) <- descend(n_fid, fes)
      } yield (n_fid, arg::args)
    }
    def getApps(prods : IntMap[Set[Production]]) : List[(FunId, CncType, List[CncType])] = {
      def toApp(fid : FId, p : Production) : List[(FunId, CncType, List[CncType])] = p match {
        case PApply(funid, pargs) => 
          val (ty,_,_,_) = pgf.abstr.funs(f)
          val (args, res) = ty.catSkeleton
          List((funid, (res, fid), args zip pargs.map(_.fid)))
        case PCoerce(fid) => prods.get(fid).map(_.toList.flatMap(toApp(fid, _))).getOrElse(Nil) 
      }
      mb_cty match {
        case Some((cat, fid)) => prods.get(fid).map(_.toList.flatMap(toApp(fid, _))).getOrElse(Nil)
        case None => (for {(fid, set) <- prods; prod <- set} yield toApp(fid, prod)).toList.flatten
      }
    }
    cnc.lproductions.get(f) match {
      case Some(prods) => for {
        (funid, (cat, fid), ctys) <- getApps(prods)
        (n_fid, args) <- descend(n_fid, ctys zip es)
      } yield (n_fid+1, Linearization((cat, n_fid), fid, f, List(e0), LinTable(cnc, _ => true, xs, funid, args)))
      case None => df(mb_cty, n_fid, e0, ys, xs, ("[" ++ f.value ++ "]"))
    }
  }
  private def df(mb_cty : Option[CncType], n_fid : FId, e0 : Expr, 
      ys : List[CId], xs : List[CId], s : String) : List[(FId, Linearization)] = mb_cty match {
    case Some((cat, fid)) => cnc.lindefs.get(fid) match {
      case Some(funs) => for {
        funid <- funs
        val args = List(Linearization((wildCId, n_fid), fidString, wildCId, List(e0), LinTable(Nil, ss(s))))
      } yield (n_fid+2, Linearization((cat, n_fid+1), fid, wildCId, List(e0), LinTable(cnc, _ => true, xs, funid, args)))
      case None => 
        if (isPredefFId(fid)) List((n_fid+2, Linearization((cat, n_fid+1), fid, wildCId, List(e0), LinTable(xs, ss(s)))))
        else for {
          PCoerce(fid) <- cnc.productions.get(fid).map(_.toList).getOrElse(Nil)
          r <- df(Some((cat, fid)), n_fid, e0, ys, xs, s)
        } yield r
    }
    case None => Nil
  }
}