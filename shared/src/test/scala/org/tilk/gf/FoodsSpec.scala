package org.tilk.gf

class FoodsSpec extends UnitSpec {
  val is = getClass.getResourceAsStream("/Foods.pgf")
  val data = Stream.continually(is.read).takeWhile(_ != -1).map(_.toByte).toArray
  val langs = List("Eng", "Fre", "Ger", "Ita")
  var pgf : PGF = null
  "The Foods grammar" should {
    "parse correctly" in {
      pgf = PGF(data)
    }
    "be named Foods" in {
      assert(pgf.absname.value == "Foods")
    }
    "have languages Eng, Fre, Ger, Ita" in {
      val pgflangs = pgf.concr.map(_._1.value)
      assert (pgflangs == langs.map(pgf.absname.value ++ _))
    }
  }
  val sentences = List(
    "Eng" -> "this cheese is fresh", 
    "Eng" -> "these delicious wines are very very Italian",
    "Ger" -> "jene frischen Fische sind teuer",
    "Fre" -> "cette pizza chaude est très ennuyeuse",
    "Ita" -> "questa pizza italiana è molto molto molto italiana"
  )
  for ((lang, str) <- sentences) {
    ("The sentence " ++ str) should {
      var es : List[Expr] = null
      var bs : BracketedString = null
      "parse correctly" in {
        val (ParseOk(es1), bs1) = pgf.parse(CId(lang), str)
        es = es1; bs = bs1
      }
      "with at least one result" in {
        assert(es.size >= 1)
      }
      "with correct bracketing" in {
        assert(bs.flatten.mkString(" ") == str)
      }
      "linearize to itself" in {
        assert(pgf.linearize(CId(lang), es.head) == str)
      }
      "linearize to other languages correctly" in {
        for (lang1 <- langs) {
          val str1 = pgf.linearize(CId(lang1), es.head)
          val (ParseOk(es1), _) = pgf.parse(CId(lang1), str1)
          assert(es1.size >= 1)
          assert(es1.contains(es1.head))
        }
      }
    }
  }
}