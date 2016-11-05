package org.tilk.gf

import scala.collection.GenTraversableOnce
import scala.collection.immutable.IntMap
import scala.collection.generic.{FilterMonadic, CanBuildFrom}
import scalaz._
import Scalaz._

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

final case class TType(e : Env, t : Type)

final case class Scope(gamma : List[(CId, TType)]) {
  def size = gamma.length
  def vars = gamma.map(_._1)
  def env : Env = {
    val n = size
    for (i <- 0 to (n-1)) yield VGen(n-i-1, Nil)
  }.toList
  def getVar(i : Int) = gamma(i)
  def lookupVar(x : CId) = for (((y, tty), i) <- gamma.zip(0 to size); if x == y) yield (i, tty)
  def addScopedVar(x : CId, tty : TType) = Scope((x,tty)::gamma)
}

object Scope {
  val empty = Scope(Nil)
}

abstract sealed class MetaValue[S]
case class MUnbound[S](s : S, scope : Scope, tty : TType, cs : List[Expr => TcM[S, Unit]]) extends MetaValue[S]
case class MBound[S](e : Expr) extends MetaValue[S]
case class MGuarded[S](e : Expr, cs : List[Expr => TcM[S, Unit]], x : Int) extends MetaValue[S] 

abstract class Selector[S] {
  def splitSelector(s : S) : (S, S)
  def select(cid : CId, scope : Scope, x : Option[Int]) : TcM[S, (Expr, TType)]
}

object Selector {
  implicit object FIdSelector extends Selector[FId] {
    def splitSelector(fid : FId) = (fid, fid)
    def select(cid : CId, scope : Scope, x : Option[Int]) = TcM.TcMMonad.raiseError(UnknownCat(cid)) // TODO
  }  
}

sealed abstract class TcM[S : Selector, A] {
  def apply[R](a : Abstr, k : A => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) : (IntMap[MetaValue[S]], S) => R => R
  
  def plus(other : TcM[S, A]) = TcM.TcMMonad[S].plus(this, other)
  def map[B](f : A => B) = TcM.TcMMonad[S].map[A,B](this)(f)
  def flatMap[B] = TcM.TcMMonad[S].bind[A,B](this)(_)
  def foreach[U](f: (A) ⇒ U) = { map(f); () }
//  def withFilter(implicit s : Selector[S]) = TcM.TcMMonadPlus[S].filter(this)(_)
  def raiseError(e : TcError) = TcM.TcMMonad[S].raiseError[TcError](e)
  
  def run(abstr : Abstr, ms : IntMap[MetaValue[S]], s : S) : (List[(S,TcError)],List[(IntMap[MetaValue[S]],S,A)]) = 
    this.apply[(List[(S,TcError)],List[(IntMap[MetaValue[S]],S,A)])](abstr,
      {(x) => (ms : IntMap[MetaValue[S]], s : S) => (b : (List[(S,TcError)],List[(IntMap[MetaValue[S]],S,A)])) => 
        val (es, xs) = b; (es, (ms, s, x) :: xs)},
      {(e : TcError, s : S) => (b : (List[(S,TcError)],List[(IntMap[MetaValue[S]],S,A)])) => 
        val (es, xs) = b; ((s, e) :: es, xs)})(ms, s)((List(), List()))
}

class TcMMonad[S : Selector] extends Monad[TcM.T[S]#T]
with MonadPlus[TcM.T[S]#T]
with MonadState[TcM.T[S]#T, S]
with MonadError[TcM.T[S]#T, TcError] {
  override def bind[A, B](x : TcM[S, A])(f: A ⇒ TcM[S, B]) = new TcM[S, B] {
    override def apply[R](abstr : Abstr, k : B => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      x(abstr, (x : A) => f(x)(abstr, k, h), h)
  }  
  override def map[A, B](x : TcM[S, A])(f : A => B) = new TcM[S, B] {
    override def apply[R](abstr : Abstr, k : B => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      x(abstr, k compose f, h)
  }
  override def point[A](a : => A) = new TcM[S, A] {
    override def apply[R](abstr : Abstr, k : A => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = k(a)    
  }  

  override def empty[A] = new TcM[S, A] { 
    override def apply[R](abstr : Abstr, k : A => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = 
      (ms : IntMap[MetaValue[S]], s : S) => (r : R) => r
  }
  override def plus[A](x : TcM[S, A], y : => TcM[S, A]) = new TcM[S, A] {
    override def apply[R](abstr : Abstr, k : A => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      (ms : IntMap[MetaValue[S]], s : S) => {
        val (s1, s2) = implicitly[Selector[S]].splitSelector(s)
        x(abstr, k, h)(ms, s1) compose y(abstr, k, h)(ms, s2)
      }
  }

  def get = new TcM[S, S] {
    override def apply[R](abstr : Abstr, k : S => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = 
      (ms : IntMap[MetaValue[S]], s : S) => k(s)(ms, s)
  }
  def init = get
  def put(s : S) = new TcM[S, Unit] {
    override def apply[R](abstr : Abstr, k : Unit => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = 
      (ms : IntMap[MetaValue[S]], _ : S) => k(())(ms, s)
  }

  def raiseError[A](e : TcError) = new TcM[S, A] {
    override def apply[R](abstr : Abstr, k : A => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = 
      (ms : IntMap[MetaValue[S]], s : S) => h(e, s)
  }
  def handleError[A](x : TcM[S,A])(fh : TcError => TcM[S, A]) = new TcM[S, A] {
    override def apply[R](abstr : Abstr, k : A => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      (ms : IntMap[MetaValue[S]], s : S) => x(abstr, k, (e, s) => fh(e)(abstr, k, h)(ms, s))(ms, s)
  }
}

object TcM {
  type T[S] = {type T[a] = TcM[S,a]}
  
  implicit def TcMMonad[S : Selector] = new TcMMonad[S]()
  
  def empty[S : Selector, A] = TcMMonad[S].empty[A]
  def point[S : Selector, A](v : A) = TcMMonad[S].point[A](v)
  def get[S : Selector] = TcMMonad[S].get
  def put[S : Selector](v : S) = TcMMonad[S].put(v)
  
  private def refineExpr_[S : Selector](ms : IntMap[MetaValue[S]], expr : Expr) : Expr = expr match {
    case EAbs(b, x, e) => EAbs(b, x, refineExpr_(ms, e))
    case EApp(e1, e2) => EApp(refineExpr_(ms, e1), refineExpr_(ms, e2))
    case ELit(l) => ELit(l)
    case EMeta(i) => ms.get(i) match {
      case Some(MBound(e)) => refineExpr_(ms, e)
      case Some(MGuarded(e,_,_)) => refineExpr_(ms, e)
      case _ => EMeta(i)
    }
    case EFun(f) => EFun(f)
    case EVar(i) => EVar(i)
    case ETyped(e, ty) => ETyped(refineExpr_(ms, e), refineType_(ms, ty))
    case EImplArg(e) => EImplArg(refineExpr_(ms, e))
  }
  
  private def refineType_[S : Selector](ms : IntMap[MetaValue[S]], tp : Type) : Type = tp match {
    case Type(hyps, cat, es) => Type(for (Hypo(b, x, ty) <- hyps) yield Hypo(b, x, refineType_(ms, ty)), cat, es.map(refineExpr_(ms, _)))
  }
  
  def refineExpr[S : Selector](e : Expr) = new TcM[S, Expr] {
    override def apply[R](abstr : Abstr, k : Expr => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      (ms : IntMap[MetaValue[S]], s : S) => k(refineExpr_(ms, e))(ms, s)
  }
  
  def refineType[S : Selector](tp : Type) = new TcM[S, Type] {
    override def apply[R](abstr : Abstr, k : Type => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      (ms : IntMap[MetaValue[S]], s : S) => k(refineType_(ms, tp))(ms, s)    
  }
  
  def generateForForest[S : Selector](e : Expr) = refineExpr[S](e)
  
  def newMeta[S : Selector](scope : Scope, tty : TType) = new TcM[S, MetaId] {
    override def apply[R](abstr : Abstr, k : MetaId => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = {
      (ms : IntMap[MetaValue[S]], s : S) => val metaid = ms.size + 1; k(metaid)(ms+((metaid, MUnbound(s, scope, tty, Nil))), s)
    }
  }
  
  def newGuardedMeta[S : Selector](e : Expr) = new TcM[S, MetaId] {
    override def apply[R](abstr : Abstr, k : MetaId => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = {
      (ms : IntMap[MetaValue[S]], s : S) => val metaid = ms.size + 1; k(metaid)(ms+((metaid, MGuarded(e, Nil, 0))), s)
    }
  }
  
  def lookupCatHyps[S : Selector](cat : CId) = new TcM[S, List[Hypo]] {
    override def apply[R](abstr : Abstr, k : List[Hypo] => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = {
      (ms : IntMap[MetaValue[S]], s : S) => abstr.cats.get(cat) match {
        case Some((hyps,_,_)) => k(hyps)(ms, s)
        case None => h(UnknownCat(cat), s)
      }
    }
  }

  def lookupFunType[S : Selector](fun : CId) = new TcM[S, Type] {
    override def apply[R](abstr : Abstr, k : Type => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = {
      (ms : IntMap[MetaValue[S]], s : S) => abstr.funs.get(fun) match {
        case Some((ty,_,_,_)) => k(ty)(ms, s)
        case None => h(UnknownFun(fun), s)
      }
    }
  }
  
  def getMeta[S : Selector](i : MetaId) = new TcM[S, MetaValue[S]] {
    override def apply[R](abstr : Abstr, k : MetaValue[S] => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = {
      (ms : IntMap[MetaValue[S]], s : S) => k(ms(i))(ms, s)
    }
  }
  
  def setMeta[S : Selector](i : MetaId, mv : MetaValue[S]) = new TcM[S, Unit] {
    override def apply[R](abstr : Abstr, k : Unit => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) = {
      (ms : IntMap[MetaValue[S]], s : S) => k(())(ms + (i, mv), s)
    }
  }
  
  def addConstraint[S : Selector](i : MetaId, j : MetaId, c : Expr => TcM[S, Unit]) : TcM[S, Unit] = {
    def addRef : TcM[S, Unit] = getMeta(i).flatMap { case MGuarded(e, cs, x) => setMeta(i, MGuarded(e, cs, x+1)) }
    def release : TcM[S, Unit] = getMeta(i).flatMap {
      case MGuarded(e, cs, x) => 
        if (x == 1) setMeta(i, MGuarded(e, cs, 0)) >> cs.map{c => c(e)}.sequence_[TcM.T[S]#T, Unit]
        else setMeta(i, MGuarded(e, cs, x-1))
    }
    getMeta(j).flatMap {
      case MUnbound(s, scope, tty, cs) => addRef >> setMeta(j, MUnbound(s, scope, tty, ((e : Expr) => release >> c(e)) :: cs))
      case MBound(e) => c(e)
      case MGuarded(e, cs, x) => 
        if (x == 0) c(e)
        else addRef >> setMeta(j, MGuarded(e, ((e : Expr) => release >> c(e)) :: cs, x)) 
    }
  }
}

object TypeCheck {
  def lookupMeta[S](ms : IntMap[MetaValue[S]])(i : Int) = ms.get(i) match {
    case Some(MBound(t)) => Some(t)
    case Some(MGuarded(t, _, x)) => if (x == 0) Some(t) else None
    case Some(MUnbound(_,_,_,_)) => None
    case None => None
  }
  def infExpr[S : Selector](scope : Scope, e : Expr) : TcM[S, (Expr, TType)] = e match {
    // TODO
    case _ => TcM.TcMMonad[S].raiseError(CannotInferType(scope.vars, e))
  }
  def tcExpr[S : Selector](scope : Scope, e : Expr, tty : TType) : TcM[S, Expr] = e match {
    // TODO
    case EMeta(_) => for (i <- TcM.newMeta(scope, tty)) yield EMeta(i)
    case e0 => for {
      (e0, tty0) <- infExpr[S](scope, e0)
      (e0, tty0) <- appImplArg(scope, e0, tty0)
      i <- TcM.newGuardedMeta(e0)
      () <- eqType(scope, scope.size, i, tty, tty0)
    } yield EMeta(i)
  }
  def eqType[S : Selector](scope : Scope, k : Int, i0 : MetaId, tty1 : TType, tty2 : TType) : TcM[S, Unit] = {
    val TType(delta1, Type(hyps1, cat1, es1)) = tty1
    val TType(delta2, Type(hyps2, cat2, es2)) = tty2
    def raiseTypeMatchError[A] = for {
      ty1 <- evalType(k, tty1)
      ty2 <- evalType(k, tty2)
      e <- TcM.refineExpr(EMeta(i0))
      v <- TcM.TcMMonad.raiseError[A](TypeMismatch(scope.vars, e, ty1, ty2))
    } yield v
    def eqHyps(k : Int, delta1 : Env, h1s : List[Hypo], delta2 : Env, h2s : List[Hypo]) : TcM[S, (Int, Env, Env)] = (h1s, h2s) match {
      case (Nil, Nil) => (k, delta1, delta2).pure[TcM.T[S]#T]
      case (Hypo(_, x, ty1) :: h1s, Hypo(_, y, ty2) :: h2s) => eqType(scope, k, i0, TType(delta1, ty1), TType(delta2, ty2)) >>
        (if (x == wildCId && y == wildCId) eqHyps(k, delta1, h1s, delta2, h2s)
        else if (x != wildCId && y != wildCId) eqHyps(k+1, VGen(k, Nil) :: delta1, h1s, VGen(k, Nil) :: delta2, h2s)
        else raiseTypeMatchError)
    }
    if (cat1 == cat2) for {
      (k, delta1, delta2) <- eqHyps(k, delta1, hyps1, delta2, hyps2)
      v <- (es1 zip es2).map {case (e1, e2) => eqExpr(raiseTypeMatchError, 
          TcM.addConstraint(i0, _, _ : Expr => TcM[S, Unit]), k, delta1, e1, delta2, e2)}.sequence_[TcM.T[S]#T, Unit]
    } yield v 
    else raiseTypeMatchError
  }
  def appImplArg[S : Selector](scope : Scope, e : Expr, tty : TType) : TcM[S, (Expr, TType)] = tty match {
    // TODO
    case _ => (e, tty).pure[TcM.T[S]#T]
  }
  def eqExpr[S : Selector](fail : TcM[S, Unit], suspend : (MetaId, Expr => TcM[S, Unit]) => TcM[S, Unit], k : Int, env1 : Env, e1 : Expr, env2 : Env, e2 : Expr) : TcM[S, Unit] = for {
    v1 <- eval(env1, e1)
    v2 <- eval(env2, e2)
    v <- eqValue(fail, suspend, k, v1, v2)
  } yield v
  def eqValue[S : Selector](fail : TcM[S, Unit], suspend : (MetaId, Expr => TcM[S, Unit]) => TcM[S, Unit], k : Int, v1 : Value, v2 : Value) : TcM[S, Unit] = {
    def deRef(v : Value) : TcM[S, Value] = v match {
      case VMeta(i, env, vs) => TcM.getMeta(i).flatMap {
        case MBound(e) => apply(env, e, vs)
        case MGuarded(e, _, x) => if (x == 0) apply(env, e, vs) else v.pure[TcM.T[S]#T]  
        case MUnbound(_, _, _, _) => v.pure[TcM.T[S]#T]
      }
      case _ => v.pure[TcM.T[S]#T]
    }
    def bind(i : Int, scope : Scope, cs : List[Expr => TcM[S, Unit]], env : Env, vs0 : List[Value], v : Value) : TcM[S, Unit] = {
      val k = scope.size
      val vs = env.take(k).reverse ++ vs0
      val xs = (for (VGen(i, Nil) <- vs) yield i).toSet.toList
      def addLam(vs : List[Value], e : Expr) : Expr = vs match {
        case Nil => e
        case v :: vs => EAbs(Explicit, CId("v"), addLam(vs, e))
      }
      if (vs.length != xs.length) suspend(i, e => apply(env, e, vs0).flatMap(iv => eqValue(fail, suspend, k, iv, v)))
      else for {
        v <- occurCheck(i, k, xs, v)
        e0 <- value2expr(xs.length, v)
        val e = addLam(vs0, e0)
        () <- TcM.setMeta[S](i, MBound(e))
        r <- cs.map(c => c(e)).sequence_[TcM.T[S]#T, Unit]
      } yield r
    }
    def occurCheck(i0 : Int, k : Int, xs : List[Int], v : Value) : TcM[S, Value] = v match {
      // TODO
      case VLit(l) => v.pure[TcM.T[S]#T]
    }
    def eqValue1(k : Int, v1 : Value, v2 : Value) : TcM[S, Unit] = (v1, v2) match {
      // TODO
      case (VSusp(i, env, vs1, c), v2) => suspend(i, e => apply(env, e, vs1).flatMap(v1 => eqValue(fail, suspend, k, c(v1), v2))) 
      case (v1, VSusp(i, env, vs2, c)) => suspend(i, e => apply(env, e, vs2).flatMap(v2 => eqValue(fail, suspend, k, v1, c(v2)))) 
      case (VMeta(f1, env1, vs1), VMeta(f2, env2, vs2)) if f1 == f2 => (vs1 zip vs2).traverse_[TcM.T[S]#T] { case(v1, v2) => eqValue(fail, suspend, k, v1, v2) }
      case (VMeta(i, env1, vs1), v2) => TcM.getMeta(i).flatMap {
        case MUnbound(_, scopei, _, cs) => bind(i, scopei, cs, env1, vs1, v2)
        case MGuarded(e, cs, x) => TcM.setMeta(i, MGuarded(e, {(e:Expr) => apply(env1, e, vs1).flatMap(v1 => eqValue1(k, v1, v2))} :: cs, x))
      }
      case (v1, VMeta(i, env2, vs2)) => TcM.getMeta(i).flatMap {
        case MUnbound(_, scopei, _, cs) => bind(i, scopei, cs, env2, vs2, v1)
        case MGuarded(e, cs, x) => TcM.setMeta(i, MGuarded(e, {(e:Expr) => apply(env2, e, vs2).flatMap(v2 => eqValue1(k, v1, v2))} :: cs, x))
      }
      case (VApp(f1, vs1), VApp(f2, vs2)) if f1 == f2 => (vs1 zip vs2).traverse_[TcM.T[S]#T] { case(v1, v2) => eqValue(fail, suspend, k, v1, v2) }
      case (VConst(f1, vs1), VConst(f2, vs2)) if f1 == f2 => (vs1 zip vs2).traverse_[TcM.T[S]#T] { case(v1, v2) => eqValue(fail, suspend, k, v1, v2) }
      case (VLit(l1), VLit(l2)) if l1 == l2 => ().pure[TcM.T[S]#T]
      case (VGen(f1, vs1), VGen(f2, vs2)) if f1 == f2 => (vs1 zip vs2).traverse_[TcM.T[S]#T] { case(v1, v2) => eqValue(fail, suspend, k, v1, v2) }
      case (VClosure(env1, EAbs(_, x1, e1)), VClosure(env2, EAbs(_, x2, e2))) => 
        val v = VGen(k, Nil)
        eqExpr(fail, suspend, k+1, v::env1, e1, v::env2, e2)
      case (VClosure(env1, EAbs(_, x1, e1)), v2) => 
        val v = VGen(k, Nil)
        for {
          v1 <- eval(v::env1, e1)
          v2 <- applyValue(v2, List(v))
          v <- eqValue(fail, suspend, k+1, v1, v2) 
        } yield v
      case (v1, VClosure(env2, EAbs(_, x2, e2))) => 
        val v = VGen(k, Nil)
        for {
          v1 <- applyValue(v1, List(v))
          v2 <- eval(v::env2, e2)
          v <- eqValue(fail, suspend, k+1, v1, v2) 
        } yield v
      case (_, _) => fail
    }
    for {
      v1a <- deRef(v1)
      v2a <- deRef(v2)
      v <- eqValue1(k, v1, v2)
    } yield v
  }
  def evalType[S : Selector](k : Int, tty : TType) : TcM[S, Type] = {
    val TType(delta, ty) = tty
    def evalTy(k : Int, delta : Env, tp : Type) : TcM[S, Type] = for {
      (k, delta, hyps) <- evalHypos(k, delta, tp.hypo)
      es <- tp.exprs.traverse[TcM.T[S]#T, Expr](e => for (v <- eval(delta, e); e2 <- value2expr(k, v)) yield e2)
    } yield Type(hyps, ty.start, es)
    def evalHypos(k : Int, delta : Env, hypos : List[Hypo]) : TcM[S, (Int, Env, List[Hypo])] = hypos match {
      case Nil => (k, delta, List[Hypo]()).pure[TcM.T[S]#T]
      case Hypo(b, x, ty) :: hyps => for {
        ty <- evalTy(k, delta, ty)
        (k, delta, hyps) <- if (x == wildCId) evalHypos(k, delta, hyps) else evalHypos(k+1, VGen(k, Nil) :: delta, hyps)
      } yield (k, delta, Hypo(b, x, ty) :: hyps)
    }
    evalTy(k, delta, ty)
  }
  def eval[S : Selector](env : Env, e : Expr) : TcM[S, Value] = new TcM[S, Value] {
    override def apply[R](abstr : Abstr, k : Value => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      (ms : IntMap[MetaValue[S]], s : S) => k(e.eval(Sig(abstr.funs, lookupMeta(ms)), env))(ms, s)
  }
  def apply[S : Selector](env : Env, e : Expr, vs : List[Value]) : TcM[S, Value] = new TcM[S, Value] {
    override def apply[R](abstr : Abstr, k : Value => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      (ms : IntMap[MetaValue[S]], s : S) => k(e.apply(Sig(abstr.funs, lookupMeta(ms)), env, vs))(ms, s)
  }
  def applyValue[S : Selector](v : Value, vs : List[Value]) : TcM[S, Value] = new TcM[S, Value] {
    override def apply[R](abstr : Abstr, k : Value => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      (ms : IntMap[MetaValue[S]], s : S) => k(v.apply(Sig(abstr.funs, lookupMeta(ms)), vs))(ms, s)
  }
  def value2expr[S : Selector](i : Int, v : Value) = new TcM[S, Expr] {
    override def apply[R](abstr : Abstr, k : Expr => (IntMap[MetaValue[S]], S) => R => R, h : (TcError, S) => R => R) =
      (ms : IntMap[MetaValue[S]], s : S) => k(v.toExpr(Sig(abstr.funs, lookupMeta(ms)), i))(ms, s)
  }
}