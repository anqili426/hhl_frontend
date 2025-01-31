package viper.HHLVerifier.generation

import viper.HHLVerifier.generation.Generator.translateType
import viper.HHLVerifier.{Id, Type}
import viper.silver.{ast => vpr}

// All functionality regarding States and the corresponding domain
object State {
  // Frequently used constants
  val getFuncPrefix = "get_"
  val stateDomainName = "State"
  val equalFuncName = "equal_on_everything_except"
  val axiomPrefix = "equal_on_everything_except_def_"
  val identType = vpr.Int

  // Associated types
  val stateType = vpr.DomainType(stateDomainName, Map.empty)(Seq.empty)

  def identifier(name: String): vpr.LocalVarDecl = vpr.LocalVarDecl(name, identType)()
  def localVar(name: String): vpr.LocalVar = vpr.LocalVar(name, stateType)()
  def localVarDecl(name: String): vpr.LocalVarDecl = vpr.LocalVarDecl(name, stateType)()

  def get(state: vpr.LocalVar, id: Id): vpr.DomainFuncApp = apply(
    getFuncPrefix + id.typ.toString(),
    Seq(
      state,
      vpr.LocalVar(id.name, identType)()
    ),
    translateType(id.typ)
  )

//  def getGetApp(args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type] = defaultTypeVarMap): vpr.DomainFuncApp = {
//    val retTyp = typVarMap.get(typeVar).getOrElse(typeVar)
//    getDomainFuncApp(getFuncName, args, retTyp, typVarMap)
//  }

  // generates the domain
  def domain(usedTypes: Set[Type]): vpr.Domain = {
    // generate get functions
    val gets = usedTypes.map(genGetFunction).toSeq :+ genEqualFunc()
    val axioms = usedTypes.map(genAxiom).toSeq

    vpr.Domain(stateDomainName, gets, axioms)()
  }

  def getEqualExceptApp(args: Seq[vpr.Exp]): vpr.DomainFuncApp = apply(equalFuncName, args, vpr.Bool)

  private def genGetFunction(typ: Type): vpr.DomainFunc = {
    vpr.DomainFunc(
      getFuncPrefix + typ.toString(),
      Seq(
        vpr.LocalVarDecl("s", stateType)(),
        vpr.LocalVarDecl("x", vpr.Int)()
      ),
      translateType(typ)
    )(domainName = stateDomainName)
  }

  private def genEqualFunc(): vpr.DomainFunc = vpr.DomainFunc(
    equalFuncName,
    Seq(
      vpr.LocalVarDecl("s1", stateType)(),
      vpr.LocalVarDecl("s2", stateType)(),
      vpr.LocalVarDecl("x", vpr.Int)()
    ),
    vpr.Bool
  )(domainName = stateDomainName)

  private def genAxiom(typ: Type): vpr.DomainAxiom = {
    val state1Var = vpr.LocalVarDecl("s1", stateType)()
    val state2Var = vpr.LocalVarDecl("s2", stateType)()
    val idVar = vpr.LocalVarDecl("x", vpr.Int)()
    val notIdVar = vpr.LocalVarDecl("y", vpr.Int)()
    val typeID = typ.toString()
    val vprType = translateType(typ)

    vpr.NamedDomainAxiom(
      // Name of the axiom
      axiomPrefix + typeID,
      // Body of the axiom
      vpr.Forall(
        // Variables used
        Seq(state1Var, state2Var, idVar),
        // Triggers
        Seq(
          vpr.Trigger(Seq(apply(equalFuncName, Seq(state1Var.localVar, state2Var.localVar, idVar.localVar), vpr.Bool)))()
        ),
        // Expression
        vpr.Implies(
          apply(equalFuncName, Seq(state1Var.localVar, state2Var.localVar, idVar.localVar), vpr.Bool),
          vpr.Forall(
            Seq(notIdVar),
            Seq.empty,
            vpr.Implies(vpr.NeCmp(idVar.localVar, notIdVar.localVar)(),
              vpr.EqCmp(
                apply(getFuncPrefix + typeID, Seq(state1Var.localVar, notIdVar.localVar), vprType),
                apply(getFuncPrefix + typeID, Seq(state2Var.localVar, notIdVar.localVar), vprType)
              )()
            )()
          )()
        )()
      )())(domainName = stateDomainName)
  }

  private def apply(name: String, args: Seq[vpr.Exp], retType: vpr.Type): vpr.DomainFuncApp = vpr.DomainFuncApp(
    name,
    args,
    Map.empty
  )(
    pos = vpr.NoPosition,
    info = vpr.NoInfo,
    errT = vpr.NoTrafos,
    typ = retType,
    domainName = stateDomainName
  )
}
