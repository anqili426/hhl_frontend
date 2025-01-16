package viper.HHLVerifier.Generation

import viper.silver.{ast => vpr}
import viper.HHLVerifier.{BoolType, Id, IntType, MapType, SeqType, SetType, StateType, Type, UnknownException, Expr}

// TODO: Avoid collisions by modifying generator: sVarName == "s", but should be "_s",
// also append underscore to s0VarName, s1VarName, s2VarName
object TypeHandler {
  // Common constants which are used to translate states and variables
  object DefaultTypes {
    val stateType     = vpr.DomainType("State", Map.empty)(Seq.empty)
    val setStateType  = vpr.DomainType("SetState", Map.empty)(Seq.empty)
    val idType        = vpr.Int
  }

  object VarNames {
    val sVarName = "_s"
    val s0VarName = "s0"
    val s1VarName = "s1"
    val s2VarName = "s2"
    val currStatesVarName = "S"
    val tempStatesVarName = "S_temp"
    val failedStatesVarName = "S_fail"
    val tempFailedStatesVarName = "S_fail_temp"
  }

  object DomainMethods {
    val setStateDomainName = "SetState"
    val inSetFuncName = "in_set"
    val inSetForAllFuncName = "in_set_forall"
    val inSetForAllLimitedFuncName = "in_set_forall_limited"
    val inSetExistsFuncName = "in_set_exists"
    val inSetExistsLimitedFuncName = "in_set_exists_limited"
    val setUnionFuncName = "set_union"
  }

  // Generates a State variable
  def state(name: String): vpr.LocalVarDecl = vpr.LocalVarDecl(name, DefaultTypes.stateType)()

  // Generates a Set State variable
  def setState(name: String): vpr.LocalVarDecl = vpr.LocalVarDecl(name, DefaultTypes.setStateType)()

  // type for tracking variables on the viper level
  private val defaultTrackerType = vpr.Int
  // prefix for programming variables
  private val progValPrefix = ""
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
    vpr.LocalVarDecl(id.name, defaultTrackerType)()
  }

  // translate name to viper var
  def getVprVar(name: String): vpr.LocalVar = vpr.LocalVar(name, defaultTrackerType)()

  // translate type to vpr type
  def translateType(typ: Type): vpr.Type = {
    typ match {
      case t: IntType => viper.silver.ast.Int
      case t: BoolType => viper.silver.ast.Bool
      case t: SeqType => viper.silver.ast.SeqType(translateType(t.sType))
      case t: SetType => viper.silver.ast.SetType(translateType(t.sType))
      case t: MapType => viper.silver.ast.MapType(translateType(t.kType), translateType(t.vType))
      case StateType() => State.stateType
      case _ =>
        throw UnknownException("Cannot translate type " + typ)
    }
  }
}
