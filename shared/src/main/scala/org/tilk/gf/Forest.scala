package org.tilk.gf

import scala.collection.immutable.IntMap

final case class Forest(abstr : Abstr, concr : Concr, forest : IntMap[Set[Production]], root : List[(List[Symbol], List[PArg])]) {
  def getAbsTrees(arg : PArg, ty : Option[Type], dp : Option[Int]) : Either[List[(FId, TcError)], List[Expr]] = Right(Nil) // TODO
  def linearizeWithBrackets(dp : Option[Int]) : BracketedString = BSLeaf("") // TODO
}