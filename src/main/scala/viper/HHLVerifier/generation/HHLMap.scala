package viper.HHLVerifier.generation

import viper.silver.{ast => vpr}


object HHLMap {
  private val mapDomainName = "HHLMap"
  private val kTypeVarName = "K"
  private val vTypeVarName = "V"

  private object FunctionIDs {
    val cardinality = "HHLMap_card"
    val lookUp = "HHLMap_apply"
    val create = "HHLMap_empty"
    val update = "HHLMap_update"
    val disjoint = "HHLMap_disjoint"
  }

  private val kTypeVar = vpr.TypeVar(kTypeVarName)
  private val vTypeVar = vpr.TypeVar(vTypeVarName)

  // TODO: There should be function for dynmacially get path, check documentation for how to parse
  private val filePath = "/Users/paulwinkler/Desktop/hhl_frontend/src/main/scala/viper/HHLVerifier/vprSupportFiles/HHLMap.vpr"
  private val supportProgram = SupportFileParser.parseFile(filePath)

  private def typeVarMap(kType: vpr.Type, vType: vpr.Type): Map[vpr.TypeVar, vpr.Type] = Map(kTypeVar -> kType, vTypeVar -> vType)
  def domainType(kType: vpr.Type, vType: vpr.Type): vpr.DomainType = vpr.DomainType(mapDomainName, typeVarMap(kType, vType))(Seq(kTypeVar, vTypeVar))

  // creates a new Map with arbitrary arguments
  def create(args: Seq[(vpr.Exp, vpr.Exp)], kType: vpr.Type, vType: vpr.Type): vpr.DomainFuncApp = args.foldLeft(apply(FunctionIDs.create, Seq.empty, typeVarMap(kType, vType), domainType(kType: vpr.Type, vType: vpr.Type)))((a, b) => {
    update(a, b._1, b._2, kType, vType)
  })
  // updates map for key with value
  def update(map: vpr.Exp, key: vpr.Exp, value: vpr.Exp, kType: vpr.Type, vType: vpr.Type): vpr.DomainFuncApp =
    apply(FunctionIDs.update, Seq(map, key, value), typeVarMap(kType, vType), domainType(kType: vpr.Type, vType: vpr.Type))
  // accesses the element in map at key
  def lookUp(map: vpr.Exp, key: vpr.Exp, kType: vpr.Type, vType: vpr.Type): vpr.DomainFuncApp = apply(FunctionIDs.lookUp, Seq(map, key), typeVarMap(kType, vType), vType)
  // returns the cardinality of the Map
  def cardinality(map: vpr.Exp, kType: vpr.Type, vType: vpr.Type): vpr.DomainFuncApp = apply(FunctionIDs.cardinality, Seq(map), typeVarMap(kType, vType), vpr.Int)
  def disjoint(map1: vpr.Exp, map2: vpr.Exp, kType: vpr.Type, vType: vpr.Type): vpr.DomainFuncApp = apply(FunctionIDs.disjoint, Seq(map1, map2), typeVarMap(kType, vType), vpr.Bool)

  private def apply(name: String, args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type], retType: vpr.Type): vpr.DomainFuncApp = vpr.DomainFuncApp(
    name,
    args,
    typVarMap
  )(
    pos = vpr.NoPosition,
    info = vpr.NoInfo,
    errT = vpr.NoTrafos,
    typ = retType,
    domainName = mapDomainName
  )

  def getDomains(): Seq[vpr.Domain] = supportProgram.domains
}