package viper.HHLVerifier.generation

import viper.silver.{ast => vpr}

// All functionality regarding SetStates and the corresponding domain
object SetState {
  // Frequently used constants
  val sVarName = "_s"
  val setStateDomainName = "SetState"
  val inSetFuncName = "in_set"
  val inSetForAllFuncName = "in_set_forall"
  val inSetForAllLimitedFuncName = "in_set_forall_limited"
  val inSetExistsFuncName = "in_set_exists"
  val inSetExistsLimitedFuncName = "in_set_exists_limited"
  val setUnionFuncName = "set_union"

  // Associated types
  val setStateType = vpr.DomainType(setStateDomainName, Map.empty)(Seq.empty)

  def localVar(name: String): vpr.LocalVar = vpr.LocalVar(name, setStateType)()
  def localVarDecl(name: String): vpr.LocalVarDecl = vpr.LocalVarDecl(name, setStateType)()

  // generates the domain
  def domain(): vpr.Domain = {
    // necessary variables
    val sVar = State.localVarDecl("s")
    val SVar = localVarDecl("S")
    val S1Var = localVarDecl("S1")
    val S2Var = localVarDecl("S2")

    val setUnionForallAxiomBody = {
      val inS1OrS2 = vpr.Or(getInSetApp(Seq(sVar.localVar, S1Var.localVar)),
        getInSetApp(Seq(sVar.localVar, S2Var.localVar))
      )()
      val inUnion = getInSetApp(Seq(sVar.localVar, getSetUnionApp(Seq(S1Var.localVar, S2Var.localVar))))
      vpr.EqCmp(inS1OrS2, inUnion)()
    }

    val setUnionExistsAxiomBody = {
      val inS1OrS2 = vpr.Or(getInSetApp(Seq(sVar.localVar, S1Var.localVar), useForAll=false),
        getInSetApp(Seq(sVar.localVar, S2Var.localVar), useForAll=false)
      )()
      val inUnion = getInSetApp(Seq(sVar.localVar, getSetUnionApp(Seq(S1Var.localVar, S2Var.localVar))), useForAll=false)
      vpr.EqCmp(inS1OrS2, inUnion)()
    }

    vpr.Domain(
      setStateDomainName,
      // Domain functions
      Seq(
        // vpr.DomainFunc(inSetFuncName, Seq(sVar, SVar), vpr.Bool)(domainName = setStateDomainName),
        vpr.DomainFunc(inSetForAllFuncName, Seq(sVar, SVar), vpr.Bool)(domainName = setStateDomainName),
        vpr.DomainFunc(inSetExistsFuncName, Seq(sVar, SVar), vpr.Bool)(domainName = setStateDomainName),
        vpr.DomainFunc(inSetForAllLimitedFuncName, Seq(sVar, SVar), vpr.Bool)(domainName = setStateDomainName),
        vpr.DomainFunc(inSetExistsLimitedFuncName, Seq(sVar, SVar), vpr.Bool)(domainName = setStateDomainName),
        vpr.DomainFunc(setUnionFuncName, Seq(S1Var, S2Var), setStateType)(domainName = setStateDomainName)
      ),
      // Domain axioms
      Seq(
        vpr.NamedDomainAxiom(
          setUnionFuncName + "_forall_def",
          vpr.Forall(
            Seq(S1Var, S2Var),
            Seq(vpr.Trigger(Seq(getSetUnionApp(Seq(S1Var.localVar, S2Var.localVar))))()),
            vpr.Forall(
              Seq(sVar),
              Seq.empty,
              setUnionForallAxiomBody
            )()
          )()
        )(domainName = setStateDomainName),
        vpr.NamedDomainAxiom(
          setUnionFuncName + "_exists_def",
          vpr.Forall(
            Seq(S1Var, S2Var),
            Seq(vpr.Trigger(Seq(getSetUnionApp(Seq(S1Var.localVar, S2Var.localVar))))()),
            vpr.Forall(
              Seq(sVar),
              Seq.empty,
              setUnionExistsAxiomBody
            )()
          )()
        )(domainName = setStateDomainName),
        vpr.NamedDomainAxiom(
          inSetForAllLimitedFuncName + "_def",
          vpr.Forall(
            Seq(sVar, SVar),
            Seq(vpr.Trigger(Seq(getInSetApp(Seq(sVar.localVar, SVar.localVar))))()),
            vpr.EqCmp(
              getInSetApp(Seq(sVar.localVar, SVar.localVar), useLimited=true),
              getInSetApp(Seq(sVar.localVar, SVar.localVar))
            )()
          )()
        )(domainName = setStateDomainName),
        vpr.NamedDomainAxiom(
          inSetExistsLimitedFuncName + "_def",
          vpr.Forall(
            Seq(sVar, SVar),
            Seq(vpr.Trigger(Seq(getInSetApp(Seq(sVar.localVar, SVar.localVar), useForAll=false)))()),
            vpr.EqCmp(
              getInSetApp(Seq(sVar.localVar, SVar.localVar), useForAll=false, useLimited=true),
              getInSetApp(Seq(sVar.localVar, SVar.localVar), useForAll=false)
            )()
          )()
        )(domainName = setStateDomainName)
      )
    )()
  }

  def getInSetApp(args: Seq[vpr.Exp], useForAll: Boolean = true, useLimited: Boolean = false): vpr.DomainFuncApp = {
    if (useForAll && !useLimited) apply(inSetForAllFuncName, args, vpr.Bool)
    else if (!useForAll && !useLimited) apply(inSetExistsFuncName, args, vpr.Bool)
    else if (useForAll && useLimited) apply(inSetForAllLimitedFuncName, args, vpr.Bool)
    else apply(inSetExistsLimitedFuncName, args, vpr.Bool)
  }

  def getSetUnionApp(args: Seq[vpr.Exp]): vpr.DomainFuncApp = apply(setUnionFuncName, args, setStateType)

  private def apply(name: String, args: Seq[vpr.Exp], retType: vpr.Type): vpr.DomainFuncApp = vpr.DomainFuncApp(
    name,
    args,
    Map.empty
  )(
    pos = vpr.NoPosition,
    info = vpr.NoInfo,
    errT = vpr.NoTrafos,
    typ = retType,
    domainName = setStateDomainName
  )
}
