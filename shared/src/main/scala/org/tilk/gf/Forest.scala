package org.tilk.gf

import scala.collection.immutable.IntMap
import scalaz._
import Scalaz._

final case class Forest(abstr : Abstr, concr : Concr, forest : IntMap[Set[Production]], root : List[(List[Symbol], List[PArg])]) {
  def getAbsTrees(arg : PArg, ty : Option[Type], dp : Option[Int]) : Either[List[(FId, TcError)], List[Expr]] = {
    val M = TcM.TcMMonad[FId]
    import M.monadPlusSyntax
    def updateScope(hypos : List[(FId, FId)], scope : Scope, mkAbs : Expr => Expr, mb_tty : Option[TType]) : (Scope, Expr => Expr, Option[TType]) = hypos match {
      case Nil => (scope, mkAbs, mb_tty)
      case (fid, _) :: hypos =>
        val (x :: _) = if (fid == fidVar) List(wildCId)
          else for (PConst(_, EFun(x), _) <- forest(fid)) yield x
        mb_tty match {
          case Some(TType(v2::delta, Type(Hypo(bt, y, ty)::hs, c, es))) => 
            if (y == wildCId) updateScope(hypos, scope.addScopedVar(x, TType(delta, ty)), 
                mkAbs compose (e => EAbs(bt, x, e)), Some(TType(delta, Type(hs, c, es))))
            else updateScope(hypos, scope.addScopedVar(x, TType(delta, ty)), 
                mkAbs compose (e => EAbs(bt, x, e)), Some(TType(VGen(scope.size, Nil)::delta, Type(hs, c, es))))
          case None => (scope, mkAbs, None) 
        }
    }
    def goArg(rec_ : Set[FId], scope : Scope, fid : FId, p : (Expr, TType), arg : PArg) : TcM[FId, (Expr, TType)] = {
      val (e1, TType(delta, Type(Hypo(bt, x, ty) :: hs, c, es))) = p
      val z = go(rec_, scope, Some(TType(delta, ty)), arg)
      if (x == wildCId) {
        for {
          e2x <- z
          val e2 = bt match {
            case Explicit => e2x
            case Implicit => EImplArg(e2x)
          }
        } yield (EApp(e1, e2), TType(delta, Type(hs, c, es)))
      } else {
        for {
          e2 <- z
          v2 <- TypeCheck.eval(scope.env, e2)
        } yield (EApp(e1, e2), TType (v2 :: delta, Type(hs, c, es)))
      }
    }
    def goArgs(rec_ : Set[FId], scope : Scope, fid : FId, p : (Expr, TType), args : List[PArg]) : TcM[FId, (Expr, TType)] = args match {
      case Nil => TcM.point(p)
      case arg :: args => for (p1 <- goArg(rec_, scope, fid, p, arg); p2 <- goArgs(rec_, scope, fid, p1, args)) yield p2
    }
    def go(rec_ : Set[FId], scope_ : Scope, mb_tty_ : Option[TType], parg : PArg) : TcM[FId, Expr] = {
      val (scope, mkAbs, mb_tty) = updateScope(parg.hypos, scope_, (x) => x, mb_tty_)
      if (parg.fid < concr.totalCats) mb_tty match {
        case Some(tty) => for (i <- TcM.newMeta(scope, tty)) yield mkAbs(EMeta(i)) 
        case None => TcM.empty
      } else if (rec_.apply(parg.fid)) TcM.empty
      else for (
          fid0 <- TcM.get[FId]; 
          _ <- TcM.put(parg.fid);
          x <- fold(TcM.empty[FId, Expr], parg.fid) 
            {(funid, args, trees) => 
              val CncFun(fn, _) = concr.cncfuns(funid)
              (fn.isLindef match {
                case Some(_) => go(rec_ + parg.fid, scope, mb_tty, args.head)
                case None => for {
                  ty_fn <- TcM.lookupFunType(fn)
                  e <- goArgs(rec_.+(parg.fid), scope, parg.fid, (EFun(fn), TType(Nil, ty_fn)), args)
                } yield e._1
              }).map(mkAbs).plus(trees)
            }
            {(const, _, trees) => (mb_tty match {
              case Some(tty) => TypeCheck.tcExpr[FId](scope, const, tty)
              case None => TypeCheck.infExpr[FId](scope, const).map(_._1)
            }).map(mkAbs).plus(trees)};
          _ <- TcM.put(fid0)) yield x
    }
    Left(List())
  }
  def linearizeWithBrackets(dp : Option[Int]) : BracketedString = 
    BracketedToken.untoken(None, List(bracketedToken(dp)))._2.head
  def bracketedToken(dp : Option[Int]) : BracketedToken = {
    def trustedSpots(parents : Set[FId], parg : PArg) : Set[FId] = {
      val parents1 = parents + parg.fid
      def descend(p : Production) : Set[FId] = p match {
        case PApply(funid, args) => args.map(trustedSpots(parents1, _)).fold(Set.empty[FId])(_ union _)
        case PConst(c, e, _) => Set.empty
      }
      if (parg.fid < concr.totalCats || parents(parg.fid)) Set.empty
      else forest.get(parg.fid) match {
        case Some(prods) => prods.toList.map(descend).reduce(_ intersect _) + parg.fid
        case None => Set(parg.fid)
      }
    }
    val trusted = (for ((_, args) <- root) yield args.map(trustedSpots(Set.empty, _)).fold(Set.empty)(_ union _)).reduce(_ intersect _)
    def isTrusted(p : CncType) = trusted(p._2)
    def getVar(p : (FId, FId)) = 
      if (p._1 == fidVar) wildCId 
      else (for (PConst(_, EFun(x), _) <- forest.get(p._1).map(_.toList).getOrElse(Nil)) yield x).head
    def render(forest : IntMap[Set[Production]], arg : PArg) : (CncType, Int, CId, List[Expr], LinTable) = {
      val PArg(hypos, fid) = arg
      def descend(forest : IntMap[Set[Production]], p : Production) = p match {
        case PApply(funid, args) =>
          val CncFun(fun, _lins) = concr.cncfuns(funid)
          val cat = fun.isLindef match {
            case Some(cat) => cat
            case None => abstr.funs(fun)._1.start
          }
          val largs = args.map(render(forest, _))
          val ltable = LinTable(concr, isTrusted, Nil, funid, largs)
          ((cat, fid), 0, wildCId, getAbsTrees(arg, None, dp).fold(_ => Nil, x => x), ltable)
        case PCoerce(fid) => render(forest, PArg(Nil, fid))
        case PConst(cat, e, ts) => ((cat, fid), 0, wildCId, List(e), LinTable(Nil, Vector(ts.map(BTLeafKS))))
      }
      forest.get(fid).map{s => val m = s.head; (m, s-m) } match {
        case Some((p, set)) => 
          val (ct, fid1, fun, es, LinTable(_, lin)) = descend(if (set.isEmpty) forest else forest+((fid, set)), p)
          (ct, fid1, fun, es, LinTable(hypos.map(getVar), lin))
        case None => throw new Exception("wrong forest id")
      }
    }
    (for ((seq, args) <- root) yield LinTable.computeSeq(isTrusted, seq, args.map(render(forest, _)))).headOption match {
      case Some(List(bs@BTBracket(_,_,_,_,_,_))) => bs
      case Some(bss) => BTBracket(wildCId, 0, 0, wildCId, Nil, bss)
      case None => BTBracket(wildCId, 0, 0, wildCId, Nil, Nil)
    }
  }
  def fold[B](b : B, fcat : FId)(f : (FunId, List[PArg], B) => B)(g : (Expr, List[String], B) => B) : B = {
    def foldProd(p : Production, b : B) = p match {
      case PCoerce(fcat) => fold(b, fcat)(f)(g)
      case PApply(funid, args) => f(funid, args, b)
      case PConst(_, const, toks) => g(const, toks, b)
    }
    forest.get(fcat) match {
      case None => b
      case Some(s) => s.foldRight(b)(foldProd)
    }
  }
}