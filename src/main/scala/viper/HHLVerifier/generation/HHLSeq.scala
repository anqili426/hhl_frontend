package viper.HHLVerifier.generation

import viper.silver.{ast => vpr}


object HHLSeq {
  val seqDomainName = "HHLSeq"
  val typeVarName = "E"

  private object FunctionIDs {
    val empty = "HHLSeq_empty"
    val singleton = "HHLSeq_singleton"
    val append = "HHLSeq_append"
    val lookUp = "HHLSeq_index"
    val length = "HHLSeq_length"
  }

  private val typeVar = vpr.TypeVar(typeVarName)

  val axiomName = "HHLSeq"
  lazy val domains: Seq[vpr.Domain] = AxiomParser.parseAxioms(axiomName).domains

  private def typeVarMap(typ: vpr.Type): Map[vpr.TypeVar, vpr.Type] = Map(typeVar -> typ)

  // def domainType(typ: vpr.Type) = vpr.DomainType(seqDomainName, Map.empty)(Seq(typeVar))
  def domainType(typ: vpr.Type) = vpr.DomainType(seqDomainName, typeVarMap(typ))(Seq(typeVar))

  // creates a new sequence with arbitrary arguments
  def create(args: Seq[vpr.Exp], typ: vpr.Type): vpr.DomainFuncApp = args.foldLeft(apply(FunctionIDs.empty, Seq.empty, typeVarMap(typ), domainType(typ)))((a, b) => {
    val singleton = apply(FunctionIDs.singleton, Seq(b), typeVarMap(typ), domainType(typ))
    append(a, singleton, typ)
  })

  // concatenates two sequences
  def append(left: vpr.Exp, right: vpr.Exp, typ: vpr.Type): vpr.DomainFuncApp = apply(FunctionIDs.append, Seq(left, right), typeVarMap(typ), domainType(typ))

  // accesses the element in obj at index ind
  def lookUp(obj: vpr.Exp, ind: vpr.Exp, typ: vpr.Type): vpr.DomainFuncApp = apply(FunctionIDs.lookUp, Seq(obj, ind), typeVarMap(typ), typ)

  // returns the length of the seq
  def length(obj: vpr.Exp, typ: vpr.Type): vpr.DomainFuncApp = apply(FunctionIDs.length, Seq(obj), typeVarMap(typ), vpr.Int)

  private def apply(name: String, args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type], retType: vpr.Type): vpr.DomainFuncApp = vpr.DomainFuncApp(
    name,
    args,
    typVarMap
  )(
    pos = vpr.NoPosition,
    info = vpr.NoInfo,
    errT = vpr.NoTrafos,
    typ = retType,
    domainName = seqDomainName
  )
}
