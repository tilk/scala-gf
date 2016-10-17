package org.tilk.gf

import fastparse.byte.all._
import java.nio.charset.Charset

object Parser {
  implicit val utf8 = Charset.forName("UTF-8")
  def parseInt : Parser[Int] = BE.Int64.map(_.intValue)
  def parseSeq[A](ap : Parser[A]) : Parser[Seq[A]] = for {
    n <- parseInt
    l <- ap.rep(exactly=n)
  } yield l
  def parseList[A](ap : Parser[A]) = parseSeq(ap).map(_.toList)
  def parseMap[A,B](ap : Parser[A], bp : Parser[B]) = parseSeq(ap ~ bp).map{ l => Map(l:_*) }
  val parseString : Parser[String] = throw new Exception("TODO")
  val parseByteString : Parser[Bytes] = for {
    n <- parseInt
    l <- AnyBytes(n)!
  } yield l
  val parseByteStringUTF8 : Parser[String] = parseByteString.map(_.decodeString.right.get)
  def parseADT[A](f : PartialFunction[Int, Parser[A]]) : Parser[A] = for {
    tag <- Int8.map(_.toInt)
    v <- f(tag)
  } yield v
  def parseOption[A](ap : Parser[A]) : Parser[Option[A]] = parseADT {
    case 0 => Pass.map(_ => None)
    case _ => ap.map(Some(_))
  }
  val parseCId : Parser[CId] = parseByteStringUTF8.map(CId(_))
  val parseBindType : Parser[BindType] = parseADT {
    case 0 => Pass.map(_ => Explicit)    
    case 1 => Pass.map(_ => Implicit)    
  }
  val parseHypo : Parser[Hypo] = P(parseBindType ~ parseCId ~ parseType).map{p => Hypo(p._1, p._2, p._3)}
  val parseExpr : Parser[Expr] = parseADT {
    case 0 => P(parseBindType ~ parseCId ~ parseExpr).map{p => EAbs(p._1, p._2, p._3)}
    case 1 => P(parseExpr ~ parseExpr).map{p => EApp(p._1, p._2)}
    case 2 => P(parseLiteral).map(ELit(_))
    case 3 => P(parseInt).map(EMeta(_))
    case 4 => P(parseCId).map(EFun(_))
    case 5 => P(parseInt).map(EVar(_))
    case 6 => P(parseExpr ~ parseType).map(p => ETyped(p._1, p._2))
    case 7 => P(parseExpr).map(EImplArg(_))
  }
  val parsePatt : Parser[Patt] = parseADT {
    case 0 => P(parseCId ~ parseList(parsePatt)).map{p => PApp(p._1, p._2)}
    case 1 => P(parseCId).map(PVar(_))
    case 2 => P(parseCId ~ parsePatt).map{p => PAs(p._1, p._2)}
    case 3 => Pass.map(_ => PWild)
    case 4 => P(parseLiteral).map(PLit(_))
    case 5 => P(parsePatt).map(PImplArg(_))
    case 6 => P(parseExpr).map(PTilde(_))
  }
  val parseType : Parser[Type] = P(parseList(parseHypo) ~ parseCId ~ parseList(parseExpr)).map{p => Type(p._1, p._2, p._3)}
  val parseEquation : Parser[Equation] = P(parseList(parsePatt) ~ parseExpr).map(p => Equation(p._1, p._2))
  val parseLiteral = parseADT {
    case 0 => parseString.map(LStr(_))
    case 1 => parseInt.map(LInt(_))
    case 2 => BE.Float64.map(LFlt(_))
  }
  val parseAbstr : Parser[Abstr] = P(
      parseMap(parseCId, parseLiteral) ~
      parseMap(parseCId, parseType ~ parseInt ~ parseOption(parseList(parseEquation)) ~ BE.Float64) ~
      parseMap(parseCId, parseList(parseHypo) ~ parseList(BE.Float64 ~ parseCId) ~ BE.Float64)).map{p =>
        Abstr(p._1, p._2.mapValues(x => (x._1, x._2, x._3.map(p => (p, List())), x._4)), p._3)
      }
}