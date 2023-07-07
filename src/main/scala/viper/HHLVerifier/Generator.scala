package viper.HHLVerifier
import viper.silver.ast.{IntLit, Seqn}
import viper.silver.parser.NameAnalyser
import viper.silver.{ast => vpr}

object Generator {
  // State domain
  val stateDomainName = "State"
  val equalFuncName = "equal_on_everything_except"
  val getFuncName = "get"

  // SetState domain
  val setStateDomainName = "SetState"
  val inSetFuncName = "in_set"
  val setUnionFuncName = "set_union"

  val funcToDomainNameMap = Map(equalFuncName -> stateDomainName,
                                getFuncName -> stateDomainName,
                                inSetFuncName -> setStateDomainName,
                                setUnionFuncName -> setStateDomainName)

  val havocSetMethodName = "havocSet"
  val checkInvMethodName = "check_inv"

  val typeVar = vpr.TypeVar("T")
  val defaultTypeVarMap = Map(typeVar -> typeVar)
  val stateType = getConcreteStateType(defaultTypeVarMap)   // Type State[T]
  val setStateType = getConcreteSetStateType(defaultTypeVarMap) // Type SetState[T]

  val sVarName = "s"
  val s0VarName = "s0"
  val s1VarName = "s1"
  val currStatesVarName = "S"
  val tempStatesVarName = "S_temp"
  val failedStatesVarName = "S_fail"
  val tempFailedStatesVarName = "S_fail_temp"
  var failedStates = vpr.LocalVarDecl(failedStatesVarName, setStateType)()
  var tempFailedStates = vpr.LocalVarDecl(tempFailedStatesVarName, setStateType)()

  var ifCounter = 0
  var loopCounter = 0
  var alignCounter = 0
  var currLoopIndex: vpr.Exp = null
  var currLoopIndexName = "$n"

  // Flag used when translating alignment
  val isIfBlockVarName = "isIfBlock"

  var allMethods: Seq[vpr.Method] = Seq.empty
  var allFuncs: Seq[vpr.Function] = Seq.empty
  var allDomains: Seq[vpr.Domain] = Seq.empty

  var verifierOption = 0 // 0: forall 1: exists

  // This variable is used when translating declarations of proof variables
  // When set to true, use an alias for the proof variable referred to by currProofVar
  // The alias is different from its declared identifier
  var useAliasForProofVar = false
  var currProofVarName = ""

  def generate(input: HHLProgram): vpr.Program = {
    var fields: Seq[vpr.Field] = Seq.empty
    var predicates: Seq[vpr.Predicate] = Seq.empty
    var extensions: Seq[vpr.ExtensionMember] = Seq.empty

    val TtoIntMap = Map(typeVar -> vpr.Int)
    val preamble = generatePreamble(Map(typeVar -> vpr.Int))
    allDomains = allDomains ++ preamble._1
    allMethods = allMethods ++ preamble._2
    translateProgram(input, TtoIntMap)
    val p = vpr.Program(allDomains, fields, allFuncs, predicates, allMethods, extensions)()
    p
  }

  def translateProgram(input: HHLProgram, typVarMap: Map[vpr.TypeVar, vpr.Type]): Unit = {
      input.content.map(m => translateMethod(m, typVarMap))
  }

  def translateMethod(method: Method, typVarMap: Map[vpr.TypeVar, vpr.Type]): Unit = {
    val presAndPosts = method.pre ++ method.post
    if (presAndPosts.size == 0 || presAndPosts.count(p => p.quantifier == "forall") == presAndPosts.size) verifierOption = 0
    else if (presAndPosts.count(p => p.quantifier == "exists") == presAndPosts.size) verifierOption = 1
    else throw UnknownException("Method " + method.mName + " can only use hyperassertions using only either forall or exists")

    val inputStates = vpr.LocalVarDecl("S0", getConcreteSetStateType(typVarMap))()
    val outputStates = vpr.LocalVarDecl(currStatesVarName, getConcreteSetStateType(typVarMap))()
    val tempStates = vpr.LocalVarDecl(tempStatesVarName, getConcreteSetStateType(typVarMap))()
    failedStates = vpr.LocalVarDecl(failedStatesVarName, getConcreteSetStateType(typVarMap))()
    tempFailedStates = vpr.LocalVarDecl(tempFailedStatesVarName, getConcreteSetStateType(typVarMap))()

    val state = vpr.LocalVarDecl(sVarName, getConcreteStateType(typVarMap))()
    // The following statement assumes that S_fail is empty
    val assumeSFailEmpty = vpr.Inhale(vpr.Forall(
      Seq(state),
      Seq.empty,
      vpr.Not(
        getInSetApp(Seq(state.localVar, failedStates.localVar), typVarMap)
      )()
    )()
    )()

    // Arguments of the input method
    val args = method.args.map(a => vpr.LocalVarDecl(a.name, translateType(a.typ, typVarMap))())
    val translatedArgs = args :+ inputStates

    // Return variables of the input method
    val ret = method.res.map(r => vpr.LocalVarDecl(r.name, translateType(r.typ, typVarMap))())
    val retVars = ret.map(r => r.localVar)

    // Forming the preconditions
    val argsWithValues = args.map(v => vpr.EqCmp(v.localVar, vpr.IntLit(args.indexOf(v))())())
    val preAboutArgs = if (argsWithValues.isEmpty) Seq.empty else Seq(argsWithValues.reduce((e1: vpr.Exp, e2: vpr.Exp) => vpr.And(e1, e2)()))
    val pres = method.pre.map(p => translateExp(p, null, inputStates.localVar)) ++ preAboutArgs

    // Forming the postconditions
    val posts = method.post.map(p => translateExp(p, null, outputStates.localVar))

    /* Method body contains the following
    *  Local variable declaration (program variables + auxiliary variables of type SetState + isIfBlock)
    *  Assume all program variables used in the method are different
    *  Assignment S := S0
    *  Assumption that S_fail is empty
    *  The translation of the input method body
    */

    // Let S := S0
    val currStatesAssignment = vpr.LocalVarAssign(outputStates.localVar, inputStates.localVar)()
    val translatedContent = translateStmt(method.body, outputStates.localVar)

    val auxiliaryVars = translatedContent._2.filter(v => v.typ.isInstanceOf[vpr.AtomicType])
    val auxiliaryVarDecls = auxiliaryVars.map(v => vpr.LocalVarDecl(v.name, v.typ)())

    // Assume that all program variables + return variables are different by assigning a distinct value to each of them
    val progVars = method.body.allProgVars.filter(v => !method.argsMap.keySet.contains(v._1) && !method.resMap.keySet.contains(v._1))
    val translatedProgVars = progVars.map(v => vpr.LocalVar(v._1, translateType(v._2, typVarMap))()).filter(v => v.typ.isInstanceOf[vpr.AtomicType]).toList
    val allVarsToAssign = translatedProgVars ++ auxiliaryVars ++ retVars
    val assignToVars = allVarsToAssign.map(v => vpr.LocalVarAssign(v, vpr.IntLit(allVarsToAssign.indexOf(v) + args.length)())())

    val progVarDecls = progVars.map(v => vpr.LocalVarDecl(v._1, translateType(v._2, typVarMap))()).toList
    val domainTypeVarDecls = Seq(tempStates, tempFailedStates, failedStates) ++ translatedContent._2.diff(auxiliaryVars).map(v => vpr.LocalVarDecl(v.name, v.typ)())
    val localVars = progVarDecls ++ auxiliaryVarDecls ++ domainTypeVarDecls

    val methodBody = Seq(currStatesAssignment) ++ assignToVars ++ Seq(assumeSFailEmpty) ++ translatedContent._1
    val thisMethod = vpr.Method(method.mName, translatedArgs, ret :+ outputStates, pres, posts,
      Some(vpr.Seqn(methodBody, localVars)()))()
    allMethods = allMethods :+ thisMethod
  }

    /*
    * The following method returns:
    * 1. the translated statement(s)
    * 2. new auxiliary variables added during translation (happens when translating an if-else block)
    */
    def translateStmt(stmt: Stmt, currStates: vpr.LocalVar): (Seq[vpr.Stmt], Seq[vpr.LocalVar]) = {
      // A set of states
      val STmp = vpr.LocalVar(tempStatesVarName, currStates.typ)()
      // A state
      val typVarMap = currStates.typ.asInstanceOf[vpr.DomainType].partialTypVarsMap
      val state = vpr.LocalVar(sVarName, getConcreteStateType(typVarMap))()
      val stateDecl = vpr.LocalVarDecl(state.name, state.typ)()
      // Results
      var newStmts: Seq[vpr.Stmt] = Seq.empty
      var newMethods: Seq[vpr.Method] = Seq.empty
      // Translation of S_temp := havocSet()
      val havocSTmp = havocSetMethodCall(STmp)
      // Translation of S := S_temp
      val updateProgStates = vpr.LocalVarAssign(currStates, STmp)()

      stmt match {
        case CompositeStmt(stmts) =>
          // Translate each statement in the sequence
          var resStmts: Seq[vpr.Stmt] = Seq.empty
          var resNewVars: Seq[vpr.LocalVar] = Seq.empty
          var tmpRes = (resStmts, resNewVars)
          for (s <- stmts) {
            tmpRes = translateStmt(s, currStates)
            resStmts = resStmts ++ tmpRes._1
            resNewVars = resNewVars ++ tmpRes._2
          }
          (resStmts, resNewVars)

        case PVarDecl(_, _) =>
          // No translation needed here
          // The translation of variable declarations always happens when translating a viper method
          // Either in translateMethod or translateInvariantVerification
          (Seq.empty, Seq.empty)

        case ProofVarDecl(pv, p) =>
          useAliasForProofVar = true
          currProofVarName = pv.name
          val assertVarExists = vpr.Assert(
                                  vpr.Exists(Seq(getAliasForProofVar(pv, typVarMap)), Seq.empty,
                                      translateExp(p, state, currStates))())()
          useAliasForProofVar = false
          val assumeP = vpr.Inhale(translateExp(p, state, currStates))()
          newStmts = Seq(assertVarExists, assumeP)
          (newStmts, Seq.empty)

        case AssumeStmt(e) =>
          newStmts = {
            if (verifierOption == 0) {
              // ForAll
              // Assume forall s: State :: in_set(s, S_tmp) ==> in_set(s, S) && exp
              val exp = vpr.And(getInSetApp(Seq(state, currStates), typVarMap),
                                  translateExp(e, state, currStates))()
              Seq(havocSTmp, translateAssumeWithViperExpr(state, STmp, exp, typVarMap), updateProgStates)
            } else {
              // Exists
              // Assume forall s: State :: in_set(s, S) && expLeft ==> in_set(s, S_tmp)
              val expRight = getInSetApp(Seq(state, STmp), typVarMap)
              val expLeft = translateExp(e, state, currStates)
              Seq(havocSTmp, translateAssumeWithViperExpr(state, currStates, expRight, typVarMap, expLeft), updateProgStates)
            }
          }
          (newStmts, Seq.empty)

        case AssertStmt(e) =>
            val havocSFailTmp = havocSetMethodCall(tempFailedStates.localVar)
            val updateSFail = vpr.LocalVarAssign(failedStates.localVar,
                                getSetUnionApp(Seq(failedStates.localVar, tempFailedStates.localVar), typVarMap))()
            if (verifierOption == 0) {
              val exp1 = vpr.And(getInSetApp(Seq(state, currStates), typVarMap),
                translateExp(e, state, currStates))()
              val exp2 = vpr.And(getInSetApp(Seq(state, currStates), typVarMap),
                translateExp(UnaryExpr("!", e), state, currStates))()
              val stmt1 = translateAssumeWithViperExpr(state, STmp, exp1, typVarMap)
              val stmt2 = translateAssumeWithViperExpr(state, tempFailedStates.localVar, exp2, typVarMap)
              newStmts = Seq(havocSTmp, havocSFailTmp, stmt1, stmt2, updateSFail, updateProgStates)
            } else {
              val exp1Right = getInSetApp(Seq(state, STmp), typVarMap)
              val exp1Left = translateExp(e, state, currStates)
              val exp2Right = getInSetApp(Seq(state, tempFailedStates.localVar), typVarMap)
              val exp2Left = translateExp(UnaryExpr("!", e), state, currStates)
              val stmt1 = translateAssumeWithViperExpr(state, currStates, exp1Right, typVarMap, exp1Left)
              val stmt2 = translateAssumeWithViperExpr(state, currStates, exp2Right, typVarMap, exp2Left)
              newStmts = Seq(havocSTmp, havocSFailTmp, stmt1, stmt2, updateSFail, updateProgStates)
            }
            (newStmts, Seq.empty)

        case HyperAssumeStmt(e) =>
          newStmts = Seq(vpr.Inhale(translateExp(e, null, currStates))())
          (newStmts, Seq.empty)

        case HyperAssertStmt(e) =>
          newStmts = Seq(vpr.Assert(translateExp(e, null, currStates))())
          (newStmts, Seq.empty)

        case AssignStmt(left, right) =>
            val leftVar = vpr.LocalVarDecl(left.name, translateType(left.typ, typVarMap))()
            val s0 = vpr.LocalVar(s0VarName, state.typ)()
            val s1 = vpr.LocalVar(s1VarName, state.typ)()
            if (verifierOption == 0) {
              val exp = vpr.EqCmp(translateExp(left, state, currStates), translateExp(right, s0, STmp))()
              val stmt = translateHavocVarHelper(STmp, currStates, state, s0, leftVar, typVarMap, exp)
              newStmts = Seq(havocSTmp, stmt, updateProgStates)
            } else {
              val exp = vpr.EqCmp(translateExp(left, s1, STmp), translateExp(right, state, currStates))()
              val stmt = translateHavocVarHelper(currStates, STmp, state, s1, leftVar, typVarMap, exp)
              newStmts = Seq(havocSTmp, stmt, updateProgStates)
            }
            (newStmts, Seq.empty)

        case HavocStmt(id) =>
            val leftVar = vpr.LocalVarDecl(id.name, typVarMap.get(typeVar).get)()
            val s0 = vpr.LocalVar(s0VarName, state.typ)()
            val s1 = vpr.LocalVar(s1VarName, state.typ)()
            val v = vpr.LocalVarDecl("v", vpr.Int)()
            val stmt = {
              if (verifierOption == 0) translateHavocVarHelper(STmp, currStates, state, s0, leftVar, typVarMap)
              else translateHavocVarHelper(currStates, STmp, state, s1, leftVar, typVarMap,
                                            vpr.EqCmp(getGetApp(Seq(s1, leftVar.localVar), typVarMap), v.localVar)(), v)
            }
            newStmts = Seq(havocSTmp, stmt, updateProgStates)
            (newStmts, Seq.empty)

        case IfElseStmt(cond, ifStmt, elseStmt) =>
            // Define new variables to hold the states in the if and else blocks respectively
            ifCounter = ifCounter + 1
            val ifBlockStates = vpr.LocalVar(currStatesVarName + ifCounter, currStates.typ)()
            ifCounter = ifCounter + 1
            val elseBlockStates = vpr.LocalVar(currStatesVarName + ifCounter, currStates.typ)()

            // Cond satisfied
            // Let ifBlockStates := S
            val assign1 = vpr.LocalVarAssign(ifBlockStates, currStates)()
            val assumeCond = translateStmt(AssumeStmt(cond), ifBlockStates)

            // Cond not satisfied
            // Let elseBlockStates := S
            val assign2 = vpr.LocalVarAssign(elseBlockStates, currStates)()
            val assumeNotCond = translateStmt(AssumeStmt(UnaryExpr("!", cond)), elseBlockStates)

            val updateSTmp = vpr.LocalVarAssign(STmp, getSetUnionApp(Seq(ifBlockStates, elseBlockStates), typVarMap))()

            val declareBlock = ifStmt.stmts.find(s => s.isInstanceOf[DeclareStmt]).getOrElse(null)
            val reuseBlock = elseStmt.stmts.find(s => s.isInstanceOf[ReuseStmt]).getOrElse(null)

            // This feature is only supported in forall-hhl
            if (declareBlock != null) {
              alignCounter = alignCounter + 1
              // Alignment
              val declareBlockInd = ifStmt.stmts.indexOf(declareBlock)
              val reuseBlockInd = elseStmt.stmts.indexOf(reuseBlock)

              // Statements before & after declare block
              val ifStmt1 = CompositeStmt(ifStmt.stmts.slice(0, declareBlockInd))
              val ifStmt2 = CompositeStmt(ifStmt.stmts.slice(declareBlockInd + 1, ifStmt.stmts.length))

              // Statements before & after reuse block
              val elseStmt1 = CompositeStmt(elseStmt.stmts.slice(0, reuseBlockInd))
              val elseStmt2 = CompositeStmt(elseStmt.stmts.slice(reuseBlockInd + 1, elseStmt.stmts.length))

              // Translate statements before declare & reuse blocks separately
              val ifRes1 = translateStmt(ifStmt1, ifBlockStates)
              val elseRes1 = translateStmt(elseStmt1, elseBlockStates)

              // Use an auxiliary variable to distinguish between ifBlockStates && elseBlockStates
              val isIfBlock = Id(isIfBlockVarName + "_" + alignCounter)
              isIfBlock.typ = TypeInstance.intType
              val isIfBlockVpr = vpr.LocalVar(isIfBlock.name, vpr.Int)()
              val setFlagForIf = translateStmt(AssumeStmt(BinaryExpr(isIfBlock, "==", Num(1))), ifBlockStates)
              val setFlagForElse = translateStmt(AssumeStmt(BinaryExpr(isIfBlock, "==", Num(0))), elseBlockStates)

              // Get a union of the two sets of states
              val defineAlignedStates = vpr.LocalVarAssign(currStates, getSetUnionApp(Seq(ifBlockStates, elseBlockStates), typVarMap))()

              // Verify the aligned statements
              val alignedStmt = translateStmt(declareBlock, currStates)

              // Separate the two sets of states from the union
              // S_temp := havoc_set()
              // inhale forall _s: State :: in_set(_s, S_temp) ==> in_set(_s, S) && get(_s, isIfBlock) == 1
              // S1 := S_temp
              val resumeIfBlockStates = Seq(havocSTmp,
                                            vpr.Inhale(
                                              vpr.Forall(Seq(stateDecl), Seq.empty,
                                                vpr.Implies(getInSetApp(Seq(state, STmp), typVarMap),
                                                  vpr.And(getInSetApp(Seq(state, currStates), typVarMap),
                                                    vpr.EqCmp(getGetApp(Seq(state, isIfBlockVpr), typVarMap),
                                                      IntLit(1)()
                                                    )()
                                                  )()
                                                )()
                                              )()
                                            )(),
                                            vpr.LocalVarAssign(ifBlockStates, STmp)())

              val resumeElseBlockStates = Seq(havocSTmp,
                                              vpr.Inhale(
                                              vpr.Forall(Seq(stateDecl), Seq.empty,
                                                vpr.Implies(getInSetApp(Seq(state, STmp), typVarMap),
                                                  vpr.And(getInSetApp(Seq(state, currStates), typVarMap),
                                                    vpr.EqCmp(getGetApp(Seq(state, isIfBlockVpr), typVarMap),
                                                      IntLit(0)()
                                                    )()
                                                  )()
                                                )()
                                              )()
                                            )(),
                                            vpr.LocalVarAssign(elseBlockStates, STmp)())

              // Verify the rest of the statements in if/else block separately
              val ifRes2 = translateStmt(ifStmt2, ifBlockStates)
              val elseRes2 = translateStmt(elseStmt2, elseBlockStates)

              newStmts = Seq(assign1, assign2) ++ assumeCond._1 ++ assumeNotCond._1 ++ ifRes1._1 ++ elseRes1._1 ++ setFlagForIf._1 ++ setFlagForElse._1 ++ Seq(defineAlignedStates) ++ alignedStmt._1 ++ resumeIfBlockStates ++ resumeElseBlockStates ++ ifRes2._1 ++ elseRes2._1 ++ Seq(updateSTmp, updateProgStates)
              (newStmts, Seq(ifBlockStates, elseBlockStates, isIfBlockVpr) ++ ifRes1._2 ++ elseRes1._2 ++ alignedStmt._2 ++ ifRes2._2 ++ elseRes2._2)
            } else {
              // No alignment
              val ifBlock = translateStmt(ifStmt, ifBlockStates)
              val elseBlock = translateStmt(elseStmt, elseBlockStates)
              newStmts = Seq(assign1) ++ assumeCond._1 ++ ifBlock._1 ++ Seq(assign2) ++ assumeNotCond._1 ++ elseBlock._1 ++ Seq(updateSTmp, updateProgStates)
              (newStmts, Seq(ifBlockStates, elseBlockStates) ++ ifBlock._2 ++ elseBlock._2)
            }
        case DeclareStmt(_, block) =>
            val res = translateStmt(block, currStates)
            (res._1, res._2)
        case ReuseStmt(_) =>
            throw UnknownException("Reuse statement shouldn't be translated on its own")
        case WhileLoopStmt(cond, body, inv) =>
            loopCounter = loopCounter + 1
            val getSkFuncName = "get_Sk_" + loopCounter
            // Connect all invariants with && to form 1 invariant
            currLoopIndex = vpr.IntLit(0)()
            val I0 = getAllInvariants(inv, currStates)
            // Assert I(0)
            val assertI0 = vpr.Assert(I0)()
            // Verify invariant in a separate method
            newMethods = translateInvariantVerification(inv, cond, body, typVarMap)
            allMethods = allMethods ++ newMethods

            // Frame all program variables that are not modified in the loop body
            val s_prime = vpr.LocalVarDecl(if (verifierOption == 0) s0VarName else s1VarName, state.typ)()
            val vVar = vpr.LocalVarDecl("progVar", vpr.Int)()
            val frameUnmodifiedVars = {
              if (body.modifiedProgVars.isEmpty) {
                vpr.Exists(Seq(s_prime), Seq.empty,
                  vpr.And(getInSetApp(Seq(s_prime.localVar, currStates), typVarMap),
                    vpr.Forall(Seq(vVar), Seq.empty,
                        vpr.EqCmp(getGetApp(Seq(s_prime.localVar, vVar.localVar), typVarMap),
                          getGetApp(Seq(state, vVar.localVar), typVarMap))()
                    )()
                  )()
                )()
              } else {
                // varsModifiedByLoop is guanranteed to be non-empty
                val varsModifiedByLoop = body.modifiedProgVars.map(v => vpr.LocalVar(v._1, translateType(v._2))())
                vpr.Exists(Seq(s_prime), Seq.empty,
                  vpr.And(getInSetApp(Seq(s_prime.localVar, currStates), typVarMap),
                    vpr.Forall(Seq(vVar), Seq.empty,
                      vpr.Implies(
                        getAndOfExps(varsModifiedByLoop.map(t => vpr.NeCmp(vVar.localVar, t)()).toList),
                        vpr.EqCmp(getGetApp(Seq(s_prime.localVar, vVar.localVar), typVarMap),
                          getGetApp(Seq(state, vVar.localVar), typVarMap))()
                      )()
                    )()
                  )()
                )()
              }
            }
            val frameUnmodifiedVarsStmt = translateAssumeWithViperExpr(state, STmp, frameUnmodifiedVars, typVarMap)

            // Let currStates be a union of Sk's
            val k = vpr.LocalVarDecl("k", vpr.Int)()
            val zero = vpr.IntLit(0)()
            val getSkFunc = vpr.Function(getSkFuncName, Seq(k), getConcreteSetStateType(typVarMap), Seq.empty, Seq.empty, Option.empty)()
            val getSkFuncApp = vpr.FuncApp(getSkFuncName, Seq(k.localVar))(vpr.NoPosition, vpr.NoInfo, getConcreteSetStateType(typVarMap), vpr.NoTrafos)
            allFuncs = allFuncs :+ getSkFunc
            currLoopIndex = k.localVar
            val assumeUnionStates =  {
              if (verifierOption == 0) {
                val unionStates = vpr.Exists(Seq(k), Seq.empty,
                  vpr.And(vpr.GeCmp(k.localVar, zero)(),
                    vpr.And(getInSetApp(Seq(state, getSkFuncApp), typVarMap),
                      getAllInvariants(inv, getSkFuncApp)
                    )()
                  )()
                )()
                Seq(translateAssumeWithViperExpr(state, STmp, unionStates, typVarMap))
              } else {
                Seq(
                  vpr.Inhale(vpr.Forall(Seq(k), Seq.empty,
                    vpr.Implies(vpr.GeCmp(k.localVar, zero)(),
                      getAllInvariants(inv, getSkFuncApp))())())(),
                  vpr.Inhale(vpr.Forall(Seq(stateDecl, k), Seq.empty,
                    vpr.Implies(vpr.And(vpr.GeCmp(k.localVar, zero)(),
                      getInSetApp(Seq(state, getSkFuncApp), typVarMap))(),
                      getInSetApp(Seq(state, STmp), typVarMap))())())()
                )
              }
            }
            //  Assume !cond
            val notCond = translateStmt(AssumeStmt(UnaryExpr("!", cond)), currStates)
            newStmts =  Seq(assertI0) ++ Seq(havocSTmp, frameUnmodifiedVarsStmt) ++ assumeUnionStates ++ Seq(updateProgStates) ++ notCond._1
            (newStmts, Seq.empty)

        case FrameStmt(f, body) =>
          val framedExpr = translateExp(f, state, currStates)
          val assertFrame = vpr.Assert(framedExpr)()
          val translatedBody = translateStmt(body, currStates)
          val inhaleFrame = vpr.Inhale(framedExpr)()
          (Seq(assertFrame) ++ translatedBody._1 ++ Seq(inhaleFrame), translatedBody._2)
      }
    }

    def getAllInvariants(invs: Seq[Expr], currStates: vpr.Exp): vpr.Exp = {
      if (invs.isEmpty) return vpr.BoolLit(true)()
      val translatedInvs = invs.map(i => translateExp(i, null, currStates))
      getAndOfExps(translatedInvs)
    }

    def translateInvariantVerification(inv: Seq[Expr], loopGuard: Expr, body: CompositeStmt, typVarMap: Map[vpr.TypeVar, vpr.Type]): Seq[vpr.Method] = {
      val methodName = checkInvMethodName + loopCounter
      val currLoopIndexDecl = vpr.LocalVarDecl(currLoopIndexName + loopCounter, vpr.Int)()
      val inputStates = vpr.LocalVarDecl("S0", getConcreteSetStateType(typVarMap))()
      val outputStates = vpr.LocalVarDecl("SS", getConcreteSetStateType(typVarMap))()
      currLoopIndex = currLoopIndexDecl.localVar
      val In = getAllInvariants(inv, inputStates.localVar)
      currLoopIndex = vpr.Add(currLoopIndex, IntLit(1)())()
      val InPlus1 = getAllInvariants(inv, outputStates.localVar)

      val tmpStates = vpr.LocalVarDecl(tempStatesVarName, getConcreteSetStateType(typVarMap))()
      val assignToOutputStates = vpr.LocalVarAssign(outputStates.localVar, inputStates.localVar)()

      // Translation of the loop body
      val loopBody = translateStmt(body, outputStates.localVar)

      // TODO: might need to debug this part
      // Precondition 1: Loop index >= 0
      val pre1 = vpr.GeCmp(currLoopIndexDecl.localVar, IntLit(0)())()
      // Precondition 2: All program variables + auxiliary variables are different
      // (do so by assigning a distinct integer value to each of them)
      val auxiliaryVars = loopBody._2.filter(v => v.typ.isInstanceOf[vpr.AtomicType])
      // TODO: change here!!!
      val allProgVarsInBody = body.allProgVars.map(v => vpr.LocalVar(v._1, translateType(v._2, typVarMap))())
      val allAtomicProgVarsInBody = allProgVarsInBody.filter(v => v.typ.isInstanceOf[vpr.AtomicType]).toList ++ auxiliaryVars
      val nonAtomicProgVarsInBody = allProgVarsInBody.filter(v => !v.typ.isInstanceOf[vpr.AtomicType])
      val allProgVarsInBodyDecl = allAtomicProgVarsInBody.map(v => vpr.LocalVarDecl(v.name, v.typ)())
      val allProgVarsWithValues = allAtomicProgVarsInBody.map(v => vpr.EqCmp(v, vpr.IntLit(allAtomicProgVarsInBody.indexOf(v))())())
      val pre2: Seq[vpr.Exp] = if (allProgVarsWithValues.isEmpty) Seq.empty else Seq(allProgVarsWithValues.reduce((e1: vpr.Exp, e2: vpr.Exp) => vpr.And(e1, e2)()))


      // Assume loop guard
      val assumeLoopGuard = translateStmt(AssumeStmt(loopGuard), outputStates.localVar)

      val methodBody = Seq(assignToOutputStates) ++ assumeLoopGuard._1 ++ loopBody._1

      val thisMethod = vpr.Method(methodName,
          Seq(currLoopIndexDecl, inputStates) ++ allProgVarsInBodyDecl,  // args
          Seq(outputStates),  // return values
          Seq(pre1, In) ++ pre2,  // pre
          Seq(InPlus1),  // post
          Some(Seqn(methodBody, Seq(tmpStates) ++ (loopBody._2.diff(allAtomicProgVarsInBody) ++ nonAtomicProgVarsInBody).map(v => vpr.LocalVarDecl(v.name, v.typ)()))())    // body
        )()
      Seq(thisMethod)
    }

    // Returns an alias that is formed by appending a $ to v's identifier
    def getAliasForProofVar(v: ProofVar, typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.LocalVarDecl = {
      if (!useAliasForProofVar) throw UnknownException("Method getAliasForProofVar cannot be called when assertProofVar == false")
      vpr.LocalVarDecl("$" + v.name, translateType(v.typ, typVarMap))()
    }

    // Note that second argument, state, is only used to translate id
    def translateExp(e: Expr, state: vpr.LocalVar, currStates: vpr.Exp): vpr.Exp = {
      val typVarMap = if (state != null) state.typ.asInstanceOf[vpr.DomainType].partialTypVarsMap
                      else Map(typeVar -> vpr.Int)
      e match {
        case id@Id(name) =>
          // Any reference to a var is translated to get(state, var)
          val viperId = vpr.LocalVar(name, translateType(id.typ, typVarMap))()
          getGetApp(Seq(state, viperId), state.typ.asInstanceOf[vpr.DomainType].partialTypVarsMap)
        case Num(value) => vpr.IntLit(value)()
        case BoolLit(value) => vpr.BoolLit(value)()
        case BinaryExpr(left, op, right) =>
          op match {
            case "+" => vpr.Add(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "-" => vpr.Sub(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "*" => vpr.Mul(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "/" => vpr.Div(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "%" => vpr.Mod(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "&&" => vpr.And(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "||" => vpr.Or(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "==" => vpr.EqCmp(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "!=" => vpr.NeCmp(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case ">" => vpr.GtCmp(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case ">=" => vpr.GeCmp(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "<" => vpr.LtCmp(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "<=" => vpr.LeCmp(translateExp(left, state, currStates), translateExp(right, state, currStates))()
          }
        case UnaryExpr(op, e) =>
          op match {
            case "!" => vpr.Not(translateExp(e, state, currStates))()
            case "-" => vpr.Minus(translateExp(e, state, currStates))()
          }
        case av@AssertVar(name) =>
          vpr.LocalVar(name, translateType(av.typ, typVarMap))()
        case HyperAssertion(quantifier, vars, body) =>
          val variables = vars.map(v => translateAssertVarDecl(v, typVarMap))
          if (quantifier == "forall") vpr.Forall(variables, Seq.empty, translateExp(body, state, currStates))()
          else if (quantifier == "exists") vpr.Exists(variables, Seq.empty, translateExp(body, state, currStates))()
          else throw UnknownException("Unexpected quantifier " + quantifier)
        case ImpliesExpr(left, right) =>
          vpr.Implies(translateExp(left, state, currStates), translateExp(right, state, currStates))()
        case GetValExpr(s, id) =>
          val stateVar = translateExp(s, state, currStates)
          translateExp(id, stateVar.asInstanceOf[vpr.LocalVar], currStates)
        case StateExistsExpr(s) =>
          val translatedState = translateExp(s, state, currStates)
          getInSetApp(Seq(translatedState, currStates), typVarMap)
        case LoopIndex() => currLoopIndex
        case pv@ProofVar(name) =>
          if (useAliasForProofVar && currProofVarName==name) getAliasForProofVar(pv, typVarMap).localVar
          else vpr.LocalVar(name, translateType(pv.typ, typVarMap))()
        // case AssertVarDecl(vName, vType) => This is translated in a separate method below, as vpr.LocalVarDecl is of type Stmt
        case _ =>
          throw UnknownException("Unexpected expression " + e)
      }
    }

  def translateAssertVarDecl(decl: AssertVarDecl, typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.LocalVarDecl = {
    vpr.LocalVarDecl(decl.vName.name, translateType(decl.vType, typVarMap))()
  }

  // This returns a Viper assume statement that expresses the following:
  // assume forall stateVar :: in_set(state1, S1) ==> (exists state2 :: in_set(state2, S2) && equal_on_everything_except(state1, state2, varToHavoc) && extraExp)
  def translateHavocVarHelper(S1: vpr.LocalVar, S2: vpr.LocalVar, state1: vpr.LocalVar, state2: vpr.LocalVar,
                              varToHavoc: vpr.LocalVarDecl, typVarMap: Map[vpr.TypeVar, vpr.Type], extraExp: vpr.Exp = null, extraVar: vpr.LocalVarDecl = null) : vpr.Inhale = {

    var itemsInExistsExpr: Seq[vpr.Exp] = Seq(getInSetApp(Seq(state2, S2), typVarMap),
                                              getEqualExceptApp(Seq(state1, state2, varToHavoc.localVar), typVarMap))
    if (extraExp != null) itemsInExistsExpr = itemsInExistsExpr :+ extraExp
    val existsExpr = vpr.Exists(Seq(vpr.LocalVarDecl(state2.name, state2.typ)()), Seq.empty, getAndOfExps(itemsInExistsExpr))()
    translateAssumeWithViperExpr(state1, S1, existsExpr, typVarMap, extraVarDecl=extraVar)
  }

  // This returns a Viper assume statement of the form "assume forall state (, extraVar) :: in_set(state, S) (&& leftExp) => (rightExp)"
  // T is determined by the typVarMap(T -> someType)
  def translateAssumeWithViperExpr(state: vpr.LocalVar, S: vpr.LocalVar, rightExp: vpr.Exp,
                                   typVarMap: Map[vpr.TypeVar, vpr.Type], leftExp: vpr.Exp = null, extraVarDecl: vpr.LocalVarDecl = null) : vpr.Inhale = {
    val lhs = {
      val inSetExp = getInSetApp(Seq(state, S), typVarMap)
      if (leftExp != null) vpr.And(inSetExp, leftExp)()
      else inSetExp
    }
    val stateDecl = vpr.LocalVarDecl(state.name, state.typ)()
    val vars = if (extraVarDecl != null) Seq(stateDecl, extraVarDecl) else Seq(stateDecl)
    vpr.Inhale(
      vpr.Forall(
        vars,
        Seq.empty,
        vpr.Implies(
          lhs, rightExp
        )()
      )()
    )()
  }

  def translateType(typ: Type, typVarMap: Map[vpr.TypeVar, vpr.Type] = defaultTypeVarMap): vpr.Type = {
    typ match {
      case IntType() => vpr.Int
      case BoolType() => vpr.Bool
      case StateType() => getConcreteStateType(typVarMap)
      case _ =>
        throw UnknownException("Cannot translate type " + typ)
    }
  }

  def generatePreamble(typVarMap: Map[vpr.TypeVar, vpr.Type]): (Seq[vpr.Domain], Seq[vpr.Method]) = {
    val sVar = vpr.LocalVarDecl(sVarName, stateType)()
    val s1Var = vpr.LocalVarDecl("s1", stateType)()
    val s2Var = vpr.LocalVarDecl("s2", stateType)()
    val xVar = vpr.LocalVarDecl("x", typeVar)()
    val yVar = vpr.LocalVarDecl("y", typeVar)()
    val SVar = vpr.LocalVarDecl("S", setStateType)()
    val S1Var = vpr.LocalVarDecl("S1", setStateType)()
    val S2Var = vpr.LocalVarDecl("S2", setStateType)()
    val TToTMap = Map(typeVar -> typeVar)

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
              getEqualExceptApp(Seq(s1Var.localVar, s2Var.localVar, xVar.localVar), TToTMap)
            ))()),
            // Expression
            vpr.Implies(getEqualExceptApp(Seq(s1Var.localVar, s2Var.localVar, xVar.localVar), TToTMap),
              vpr.Forall(
                Seq(yVar),
                Seq.empty,
                vpr.Implies(vpr.NeCmp(xVar.localVar, yVar.localVar)(),
                                      vpr.EqCmp(getGetApp(Seq(s1Var.localVar, yVar.localVar)),
                                                getGetApp(Seq(s2Var.localVar, yVar.localVar))
                                                )()
                            )()
              )()
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
            Seq(vpr.Trigger(Seq(getSetUnionApp(Seq(S1Var.localVar, S2Var.localVar))))()),
            vpr.Forall(
              Seq(sVar),
              Seq.empty,
              vpr.EqCmp(
                vpr.Or(getInSetApp(Seq(sVar.localVar, S1Var.localVar)),
                  getInSetApp(Seq(sVar.localVar, S2Var.localVar))
                )(),
                getInSetApp(Seq(sVar.localVar, getSetUnionApp(Seq(S1Var.localVar, S2Var.localVar))))
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

    val SS = vpr.LocalVarDecl("SS", getConcreteSetStateType(typVarMap))()
    val havocSetMethod = vpr.Method(havocSetMethodName, Seq.empty, Seq(SS), Seq.empty, Seq.empty, Option.empty)()

    (Seq(stateDomain, setStateDomain), Seq(havocSetMethod))
  }

  // Connects all expressions in the input with "&&"
  def getAndOfExps(exps: Seq[vpr.Exp]): vpr.Exp = {
    if (exps.isEmpty) throw UnknownException("The input to getAndOfExps cannot be an empty sequence")
    exps.reduceLeft((e1, e2) => vpr.And(e1, e2)())
  }

  def getConcreteSetStateType(typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.Type = {
    vpr.DomainType(setStateDomainName, typVarMap)(Seq(typeVar))
  }

  def getConcreteStateType(typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.Type = {
    vpr.DomainType(stateDomainName, typVarMap)(Seq(typeVar))
  }

  def havocSetMethodCall(set: vpr.LocalVar): vpr.MethodCall = {
    vpr.MethodCall(havocSetMethodName, Seq.empty, Seq(set))(pos = vpr.NoPosition, info = vpr.NoInfo, errT = vpr.NoTrafos)
  }

  def getInSetApp(args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type] = defaultTypeVarMap): vpr.DomainFuncApp = {
    getDomainFuncApp(inSetFuncName, args, vpr.Bool, typVarMap)
  }

  def getSetUnionApp(args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type] = defaultTypeVarMap): vpr.DomainFuncApp = {
    getDomainFuncApp(setUnionFuncName, args, getConcreteSetStateType(typVarMap), typVarMap)
  }

  def getEqualExceptApp(args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type] = defaultTypeVarMap): vpr.DomainFuncApp = {
    getDomainFuncApp(equalFuncName, args, vpr.Bool, typVarMap)
  }

  def getGetApp(args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type] = defaultTypeVarMap): vpr.DomainFuncApp = {
    val retTyp = typVarMap.get(typeVar).getOrElse(typeVar)
    getDomainFuncApp(getFuncName, args, retTyp, typVarMap)
  }

  def getDomainFuncApp(funcName: String, args: Seq[vpr.Exp], retType:vpr.Type, typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.DomainFuncApp = {
    vpr.DomainFuncApp(
      funcName,
      args,
      typVarMap)(pos = vpr.NoPosition,
      info = vpr.NoInfo,
      errT = vpr.NoTrafos,
      typ = retType,
      domainName = funcToDomainNameMap.get(funcName).getOrElse("Error"))
  }
}
