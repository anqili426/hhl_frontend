package viper.HHLVerifier

import viper.silver.ast.{Type, TypeVar}
import viper.silver.{ast => vpr}

object Generator {

  val stateDomainName = "State"
  val equalFuncName = "equal_on_everything_except"
  val getFuncName = "get"

  val setStateDomainName = "SetState"
  val inSetFuncName = "in_set"
  val setUnionFuncName = "set_union"

  val typeVar = vpr.TypeVar("T")

  def generate(input: HHLProgram): vpr.Program = {
    var domains: Seq[vpr.Domain] = Seq.empty
    var fields: Seq[vpr.Field] = Seq.empty
    var functions: Seq[vpr.Function] = Seq.empty
    var predicates: Seq[vpr.Predicate] = Seq.empty
    var methods: Seq[vpr.Method] = Seq.empty
    var extensions: Seq[vpr.ExtensionMember] = Seq.empty

    val preamble = generatePreamble()
    domains = domains ++ preamble._1
    methods = methods ++ preamble._2

    // Translate the input program

    val p = vpr.Program(domains, fields, functions, predicates, methods, extensions)()
    p
  }

  def generatePreamble(): (Seq[vpr.Domain], Seq[vpr.Method]) = {
    val stateType = vpr.DomainType(stateDomainName, Map.empty)(Seq(typeVar))
    val setStateType = vpr.DomainType(setStateDomainName, Map(typeVar -> typeVar))(Seq(typeVar))

    val sVar = vpr.LocalVarDecl("s", stateType)()
    val s1Var = vpr.LocalVarDecl("s1", stateType)()
    val s2Var = vpr.LocalVarDecl("s2", stateType)()
    val xVar = vpr.LocalVarDecl("x", typeVar)()
    val yVar = vpr.LocalVarDecl("y", typeVar)()

    val SVar = vpr.LocalVarDecl("S", setStateType)()
    val S1Var = vpr.LocalVarDecl("S1", setStateType)()
    val S2Var = vpr.LocalVarDecl("S2", setStateType)()

    val stateDomain = vpr.Domain(
      stateDomainName,
      // Domain functions
      Seq(
        // function get
        vpr.DomainFunc(getFuncName,
          Seq(sVar, xVar),
          typeVar)(domainName = stateDomainName),
        // function equal_on_everything_except
        vpr.DomainFunc(equalFuncName,
          Seq(s1Var, s2Var, xVar),
          vpr.Bool)(domainName = stateDomainName)
      ),
      // Domain axioms
      Seq(
        // Axiom for function equal_on_everything_except
        vpr.NamedDomainAxiom(
          // Name of the axiom
          equalFuncName + "_def",
          // Body of the axiom
          vpr.Forall(
            // Variables used
            Seq(s1Var, s2Var, xVar),
            // Triggers
            Seq(vpr.Trigger(Seq(
              getDomainFuncApp(equalFuncName, Seq(s1Var.localVar, s2Var.localVar, xVar.localVar), stateDomainName, vpr.Bool, Map.empty)
            ))()),
            // Expression
            vpr.Forall(
              Seq(yVar),
              Seq.empty,
              vpr.Implies(getDomainFuncApp(equalFuncName, Seq(s1Var.localVar, s2Var.localVar, xVar.localVar), stateDomainName, vpr.Bool, Map.empty),
                vpr.Implies(vpr.NeCmp(xVar.localVar, yVar.localVar)(),
                  vpr.EqCmp(getDomainFuncApp(getFuncName, Seq(s1Var.localVar, xVar.localVar), stateDomainName, typeVar, Map.empty),
                    getDomainFuncApp(getFuncName, Seq(s2Var.localVar, xVar.localVar), stateDomainName, typeVar, Map.empty))())())()
            )()
          )())(domainName = stateDomainName)),
      // Type variable of the domain
      Seq(typeVar),
      // Interpretations
      Option.empty
    )()

    val setStateDomain = vpr.Domain(
      setStateDomainName,
      // Domain functions
      Seq(
        vpr.DomainFunc(inSetFuncName, Seq(sVar, SVar), vpr.Bool)(domainName = setStateDomainName),
        vpr.DomainFunc(setUnionFuncName, Seq(S1Var, S2Var), setStateType)(domainName = setStateDomainName)
      ),
      // Domain axioms
      Seq(
        vpr.NamedDomainAxiom(
          setUnionFuncName + "_def",
          vpr.Forall(
            Seq(S1Var, S2Var),
            Seq(vpr.Trigger(
              Seq(
                getDomainFuncApp(setUnionFuncName, Seq(S1Var.localVar, S2Var.localVar), setStateDomainName, setStateType, Map(typeVar -> typeVar))
              ))()
            ),
            vpr.Forall(
              Seq(sVar),
              Seq.empty,
              vpr.EqCmp(
                vpr.Or(getDomainFuncApp(inSetFuncName, Seq(sVar.localVar, S1Var.localVar), setStateDomainName, vpr.Bool, Map.empty),
                  getDomainFuncApp(inSetFuncName, Seq(sVar.localVar, S2Var.localVar), setStateDomainName, vpr.Bool, Map.empty)
                )(),
                getDomainFuncApp(inSetFuncName,
                  Seq(sVar.localVar,
                    getDomainFuncApp(setUnionFuncName, Seq(S1Var.localVar, S2Var.localVar), setStateDomainName, setStateType, Map(typeVar -> typeVar))
                  ),
                  setStateDomainName, vpr.Bool, Map.empty)
              )()
            )()
          )()
        )(domainName = setStateDomainName)
      ),
      // Type variable of the domain
      Seq(typeVar),
      // Interpretations
      Option.empty
    )()

    val SS = vpr.LocalVarDecl("SS", vpr.DomainType(setStateDomainName, Map(typeVar -> vpr.Int))(Seq(typeVar)))()
    val havocSetMethod = vpr.Method("havocSet", Seq.empty, Seq(SS), Seq.empty, Seq.empty, Option.empty)()

    (Seq(stateDomain, setStateDomain), Seq(havocSetMethod))

  }


  def getDomainFuncApp(funcName: String, args: Seq[vpr.Exp], domainName: String, retType:Type, typVarMap: Map[TypeVar, Type]): vpr.DomainFuncApp = {
    vpr.DomainFuncApp(
      funcName,
      args,
      typVarMap)(pos = vpr.NoPosition,
      info = vpr.NoInfo,
      errT = vpr.NoTrafos,
      typ = retType,
      domainName = domainName)
  }

}
