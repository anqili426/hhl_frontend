package viper.HHLVerifier.Generation

import viper.HHLVerifier.Generation.Generator.{defaultTypeVarMap, getConcreteStateType}
import viper.silver.{ast => vpr}
import viper.HHLVerifier.{BoolType, Id, IntType, MapType, SeqType, SetType, StateType, Type, UnknownException, Expr}

object TypeHandling {
  // type for tracking variables on the viper level
  private val defaultTrackerType = vpr.Int
  // prefix for programming variables
  private val progValPrefix = "pv_"
  // set containing all used types in program
  var setOfDeclaredTypes: Set[Type] = Set.empty
  // maps for tracking types of variables
  private var mapHHLTypeOfId: Map[String, Type] = Map.empty
  private var mapVprTypeOfId: Map[String, vpr.Type] = Map.empty
  // counter for generating unique variable ids - Only Access via assignId()!
  private var variablesIdCounter = 0
  // get function prefix
  private val getFuncPrefix = "get_"

  // assigns unique ids to vpr variables
  def assignId(): Int = {
    val r = variablesIdCounter
    variablesIdCounter += 1
    r
  }

  // translates params and return variables of methods
  def translateMethodVariables(params: Seq[Id]): Seq[vpr.LocalVarDecl] = params.map(declareVariable)

  // declares a variable and returns vpr declaration
  def declareVariable(id: Id): vpr.LocalVarDecl = {
    mapHHLTypeOfId = mapHHLTypeOfId + (getName(id.name) -> id.typ)
    mapVprTypeOfId = mapVprTypeOfId + (getName(id.name) -> translateTypeToVprType(id.typ))
    vpr.LocalVarDecl(progValPrefix + id.name, defaultTrackerType)()
  }

  // translate name to viper var
  def getVprVar(name: String): vpr.LocalVar = vpr.LocalVar(getName(name), defaultTrackerType)()

  // translate name
  def getName(name: String): String = progValPrefix + name

  // translate type to vpr type
  def translateTypeToVprType(typ: Type, typVarMap: Map[vpr.TypeVar, vpr.Type] = defaultTypeVarMap): vpr.Type = {
    typ match {
      case t: IntType => viper.silver.ast.Int
      case t: BoolType => viper.silver.ast.Bool
      case t: SeqType => viper.silver.ast.SeqType(translateTypeToVprType(t.subtype))
      case t: SetType => viper.silver.ast.SetType(translateTypeToVprType(t.subtype))
      case t: MapType => viper.silver.ast.MapType(translateTypeToVprType(t.keySubtype), translateTypeToVprType(t.valueSubtype))
      case StateType() => getConcreteStateType(typVarMap)
      case _ =>
        throw UnknownException("Cannot translate type " + typ)
    }
  }

  def getGetFunctionName(name: String): String =
    getFuncPrefix + mapHHLTypeOfId(getName(name)).toString()

  def getVprType(name: String): vpr.Type = mapVprTypeOfId(getName(name))
}
