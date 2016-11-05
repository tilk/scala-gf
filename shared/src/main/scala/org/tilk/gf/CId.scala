package org.tilk.gf

final case class CId(val value : String) {
  def isLindef = if (value.startsWith("lindef ")) Some(value.stripPrefix("lindef ")) else None
}