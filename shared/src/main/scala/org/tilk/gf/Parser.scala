package org.tilk.gf

import fastparse.byte.all._
import java.nio.charset.Charset
import scala.collection.immutable.IntMap

object Parser {
  implicit val utf8 = Charset.forName("UTF-8")
  val parseInt : Parser[Int] = for {
    b <- AnyByte!
    val bv = b.head.toInt & 0xff
    r <- if ((bv & 0x80) != 0) parseInt
         else Pass.map(_ => 0)
  } yield (bv&0x7f)|(r << 7)
  val parseUTF8Char : Parser[Bytes] = for {
    b <- AnyByte!
    val bv = b.head.toInt & 0xff
    r <- if (bv < 0x80) Pass.map(_ => Bytes.empty) 
         else if (bv < 0xe0) AnyByte!
         else if (bv < 0xf0) AnyBytes(2)!
         else AnyBytes(3)!
  } yield b++r
  def parseSeq[A](ap : Parser[A]) : Parser[Seq[A]] = (for {
    n <- parseInt
    l <- ap.rep(exactly=n)
  } yield l)
  def parseList[A](ap : Parser[A]) : Parser[List[A]] = parseSeq(ap).map(_.toList)
  def parseArray[A](ap : Parser[A]) : Parser[Vector[A]] = parseSeq(ap).map(_.toVector)
  def parseSet[A](ap : Parser[A]) : Parser[Set[A]] = parseSeq(ap).map(_.toSet)
  def parseMap[A,B](ap : Parser[A], bp : Parser[B]) : Parser[Map[A,B]] = parseSeq(ap ~ bp).map{ l => Map(l:_*) }
  def parseIntMap[B](bp : Parser[B]) : Parser[IntMap[B]] = parseSeq(parseInt ~ bp).map{ l => IntMap(l:_*) }
  val parseString : Parser[String] = parseSeq(parseUTF8Char).map(x => Bytes.concat(x).decodeString.right.get)
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
  val parseAbstr : Parser[Abstr] = for {
    aflags <- parseMap(parseCId, parseLiteral)
    funs <-parseMap(parseCId, parseType ~ parseInt ~ parseOption(parseList(parseEquation)) ~ BE.Float64)
    cats <-parseMap(parseCId, parseList(parseHypo) ~ parseList(BE.Float64 ~ parseCId) ~ BE.Float64)
  } yield Abstr(aflags, funs.mapValues(x => (x._1, x._2, x._3.map(p => (p, List())), x._4)), cats)
  val parseSymbol : Parser[Symbol] = parseADT {
    case 0 => P(parseInt ~ parseInt).map(p => SymCat(p._1, p._2))
    case 1 => P(parseInt ~ parseInt).map(p => SymLit(p._1, p._2))
    case 2 => P(parseInt ~ parseInt).map(p => SymVar(p._1, p._2))
    case 3 => P(parseString).map(SymKS(_))
    case 4 => P(parseList(parseSymbol) ~ parseList(parseList(parseSymbol) ~ parseList(parseString))).map(p => SymKP(p._1, p._2))
    case 5 => Pass.map(_ => SymBind)
    case 6 => Pass.map(_ => SymSoftBind)
    case 7 => Pass.map(_ => SymNE)
    case 8 => Pass.map(_ => SymSoftSpace)
    case 9 => Pass.map(_ => SymCapit)
    case 10 => Pass.map(_ => SymAllCapit)
  }
  val parseCncFun : Parser[CncFun] = P(parseCId ~ parseArray(parseInt)).map(p => CncFun(p._1, p._2))
  val parseCncCat : Parser[CncCat] = P(parseInt ~ parseInt ~ parseArray(parseString)).map(p => CncCat(p._1, p._2, p._3))
  val parsePArg : Parser[PArg] = P(parseList(parseInt) ~ parseInt).map(p => PArg(p._1.map(a => (fidVar, a)), p._2))
  val parseProduction : Parser[Production] = parseADT {
    case 0 => P(parseInt ~ parseList(parsePArg)).map(p => PApply(p._1, p._2))
    case 1 => P(parseInt).map(PCoerce(_))
  }
  val parseConcr : Parser[Concr] = for {
    cflags <- parseMap(parseCId, parseLiteral)
    printnames <- parseMap(parseCId, parseString)
    sequences <- parseArray(parseArray(parseSymbol))
    cncfuns <- parseArray(parseCncFun)
    lindefs <- parseIntMap(parseList(parseInt))
    linrefs <- parseIntMap(parseList(parseInt))
    productions <- parseIntMap(parseSet(parseProduction))
    cnccats <- parseMap(parseCId, parseCncCat)
    totalCats <- parseInt
  } yield Concr(cflags, printnames, cncfuns, lindefs, linrefs, sequences, productions, IntMap.empty, Map.empty, cnccats, IntMap.empty, totalCats)
  val pgfMajorVersion = 2
  val pgfMinorVersion = 1
  val parsePGF21 : Parser[PGF] = for {
    gflags <- parseMap(parseCId, parseLiteral)
    absname <- parseCId
    abstr <- parseAbstr
    concr <- parseMap(parseCId, parseConcr)
  } yield PGF(gflags, absname, abstr, concr)
  val parsePGF : Parser[PGF] = for {
    major <- BE.Int16
    minor <- BE.Int16
    pgf <- if (major == pgfMajorVersion && minor <= pgfMinorVersion) parsePGF21 else throw new Exception("Unsupported PGF version")
  } yield pgf
}