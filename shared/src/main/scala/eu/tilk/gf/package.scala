package eu.tilk

package object gf {
  type FId = Int
  type FunId = Int
  type SeqId = Int
  type Token = String
  type CodeLabel = Int
  type MetaId = Int
  type LIndex = Int
  type DotPos = Int
  type Env = List[Value]
  type CncType = (CId, FId)
  val fidString : FId = -1
  val fidInt : FId = -2
  val fidFloat : FId = -3
  val fidVar : FId = -4
  val cidString = CId("String")
  val cidInt    = CId("Int")
  val cidFloat  = CId("Float")
  val cidVar    = CId("__gfVar")
  val wildCId   = CId("_")
  def isPredefFId(fid : FId) = List(fidString, fidInt, fidFloat, fidVar).contains(fid)
}