package org.tilk.gf

sealed abstract class BracketedString
case class BSLeaf(token : Token) extends BracketedString
case class BSBracket(id : CId, fid : FId, idx : LIndex, cid2 : CId, exprs : List[Expr], substrings : List[BracketedString]) extends BracketedString

sealed abstract class BracketedToken
case class BTBracket(cid : CId, fid : FId, idx : LIndex, cid2 : CId, exprs : List[Expr], subtokens : List[BracketedToken]) extends BracketedToken
case class BTLeafKS(token : Token) extends BracketedToken
case object BTLeafNE extends BracketedToken
case object BTLeafBind extends BracketedToken
case object BTLeafSoftBind extends BracketedToken
case object BTLeafCapit extends BracketedToken
case class BTLeafKP(subtokens : List[BracketedToken], l : List[(List[BracketedToken], List[String])]) extends BracketedToken
