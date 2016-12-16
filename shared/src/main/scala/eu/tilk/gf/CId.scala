package eu.tilk.gf

final case class CId(val value : String) {
  def isLindef = if (value.startsWith("lindef ")) Some(CId(value.stripPrefix("lindef "))) else None
}

object CId {
  implicit object ordering extends Ordering[CId] {
    override def compare(a : CId, b : CId) = a.value compare b.value
  }
}