package viper.HHLVerifier.Generation

import viper.silver.{ast => vpr}


object HHLSeq {
  val seqDomainName = "HHLSeq"
  val typeVarName = "T"
  // function names
  val emptyConstructorFuncName = "HHLSeq_empty"
  val singletonConstructorFuncName = "HHLSeq_singleton"
  val appendFuncName = "HHLSeq_append"
  val accessFuncName = "HHLSeq_index"
  val lengthFuncName = "HHLSeq_length"

  private val typeVar = vpr.TypeVar(HHLSeq.typeVarName)
  private def typeVarMap(typ: vpr.Type) = Map(typeVar -> typ)
  def seqDomainType(typ: vpr.Type) = vpr.DomainType(HHLSeq.seqDomainName, typeVarMap(typ))(Seq(typeVar))

  // creates a new sequence with arbitrary arguments
  def create(args: Seq[vpr.Exp], typ: vpr.Type): vpr.DomainFuncApp = args.foldLeft(apply(HHLSeq.emptyConstructorFuncName, Seq.empty, typeVarMap(typ), seqDomainType(typ)))((a, b) => {
    val singleton = apply(HHLSeq.singletonConstructorFuncName, Seq(b), typeVarMap(typ), seqDomainType(typ))
    append(a, singleton, typ)
  })
  // concatenates two sequences
  def append(left: vpr.Exp, right: vpr.Exp, typ: vpr.Type): vpr.DomainFuncApp = apply(HHLSeq.appendFuncName, Seq(left, right), typeVarMap(typ), seqDomainType(typ))
  // accesses the element in obj at index ind
  def access(obj: vpr.Exp, ind: vpr.Exp, typ: vpr.Type): vpr.DomainFuncApp = apply(HHLSeq.accessFuncName, Seq(obj, ind), typeVarMap(typ), typ)
  // returns the length of the seq
  def length(obj: vpr.Exp, typ: vpr.Type): vpr.DomainFuncApp = apply(HHLSeq.lengthFuncName, Seq(obj), typeVarMap(typ), vpr.Int)

  private def apply(name: String, args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type], retType: vpr.Type): vpr.DomainFuncApp = vpr.DomainFuncApp(
    name,
    args,
    typVarMap
  )(
    pos = vpr.NoPosition,
    info = vpr.NoInfo,
    errT = vpr.NoTrafos,
    typ = retType,
    domainName = HHLSeq.seqDomainName
  )
}
