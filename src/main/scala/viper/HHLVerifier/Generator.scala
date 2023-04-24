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
  val currStatesVarName = "S"
  val tempStatesVarName = "S_temp"
  val failedStatesVarName = "S_fail"
  val tempFailedStatesVarName = "S_fail_temp"
  var failedStates = vpr.LocalVarDecl(failedStatesVarName, setStateType)()
  var tempFailedStates = vpr.LocalVarDecl(tempFailedStatesVarName, setStateType)()

  var ifCounter = 0
  var loopCounter = 0
  var currLoopIndex: vpr.Exp = null
  var currLoopIndexName = "n_loop"

  def generate(input: HHLProgram): vpr.Program = {
    var domains: Seq[vpr.Domain] = Seq.empty
    var fields: Seq[vpr.Field] = Seq.empty
    var functions: Seq[vpr.Function] = Seq.empty
    var predicates: Seq[vpr.Predicate] = Seq.empty
    var methods: Seq[vpr.Method] = Seq.empty
    var extensions: Seq[vpr.ExtensionMember] = Seq.empty

    val TtoIntMap = Map(typeVar -> vpr.Int)
    val preamble = generatePreamble(Map(typeVar -> vpr.Int))
    domains = domains ++ preamble._1
    methods = methods ++ preamble._2 ++ translateProgram(input, TtoIntMap)
    val p = vpr.Program(domains, fields, functions, predicates, methods, extensions)()
    p
  }

  def translateProgram(input: HHLProgram, typVarMap: Map[vpr.TypeVar, vpr.Type]): Seq[vpr.Method] = {
      val currStates = vpr.LocalVarDecl(currStatesVarName, getConcreteSetStateType(typVarMap))()
      val tempStates = vpr.LocalVarDecl(tempStatesVarName, getConcreteSetStateType(typVarMap))()
      failedStates = vpr.LocalVarDecl(failedStatesVarName, getConcreteSetStateType(typVarMap))()
      tempFailedStates = vpr.LocalVarDecl(tempFailedStatesVarName, getConcreteSetStateType(typVarMap))()
      val translatedContent = translateStmt(input.content, currStates)

      val localVars = Seq(currStates, tempStates, tempFailedStates, failedStates) ++ translatedContent._3
      // Assume that all program variables are different by assigning a distinct value to each of them
      val allProgVars = input.content.allProgVars.map(v => vpr.LocalVar(v._1, translateType(v._2, typVarMap))()).toList
      val assignToProgVars = allProgVars.map(v => vpr.LocalVarAssign(v, vpr.IntLit(allProgVars.indexOf(v))())())

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
      val methodBody = assignToProgVars ++ Seq(assumeSFailEmpty) ++ translatedContent._1
      val mainMethod = vpr.Method("main", Seq.empty, Seq.empty, Seq.empty, Seq.empty,
                                  Some(vpr.Seqn(methodBody, localVars)()))()
      mainMethod +: translatedContent._2
  }

    // Any statement is translated to a block of Viper code as follows:
    // S refers to the current program states, provided as input
    // S_temp := havocSet()
    //      .... (Translation uses S_temp and S)
    // S := S_temp
    // In the end, we get back S in the output
    def translateStmt(stmt: Stmt, currStates: vpr.LocalVarDecl): (Seq[vpr.Stmt], Seq[vpr.Method], Seq[vpr.LocalVarDecl]) = {
      // A set of states
      val STmp = vpr.LocalVarDecl(tempStatesVarName, currStates.typ)()
      // A state
      val typVarMap = currStates.typ.asInstanceOf[vpr.DomainType].partialTypVarsMap
      val state = vpr.LocalVarDecl(sVarName, getConcreteStateType(typVarMap))()
      // Results
      var newStmts: Seq[vpr.Stmt] = Seq.empty
      var newMethods: Seq[vpr.Method] = Seq.empty
      // Translation of S_temp := havocSet()
      val havocSTmp = havocSetMethodCall(STmp.localVar)
      // Translation of S := S_temp
      val updateProgStates = vpr.LocalVarAssign(currStates.localVar, STmp.localVar)()

      stmt match {
        case CompositeStmt(stmts) =>
          // Translate each statement in the sequence
          var resStmts: Seq[vpr.Stmt] = Seq.empty
          var resMethods: Seq[vpr.Method] = Seq.empty
          var resNewVars: Seq[vpr.LocalVarDecl] = Seq.empty
          var tmpRes = (resStmts, resMethods, resNewVars)
          for (s <- stmts) {
            tmpRes = translateStmt(s, currStates)
            resStmts = resStmts ++ tmpRes._1
            resMethods = resMethods ++ tmpRes._2
            resNewVars = resNewVars ++ tmpRes._3
          }
          (resStmts, resMethods, resNewVars)

        case PVarDecl(name, typ) =>
          val thisVar = vpr.LocalVarDecl(name.name, translateType(typ))()
          (Seq.empty, Seq.empty, Seq(thisVar))

        case AssumeStmt(e) =>
          val exp = vpr.And(getInSetApp(Seq(state.localVar, currStates.localVar), typVarMap),
                                        translateExp(e, state, currStates))()
          newStmts = Seq(havocSTmp, translateAssumeWithViperExpr(exp, state, STmp, typVarMap), updateProgStates)
          (newStmts, Seq.empty, Seq.empty)

        case AssertStmt(e) =>
            val havocSFailTmp = havocSetMethodCall(tempFailedStates.localVar)
            val exp1 = vpr.And(getInSetApp(Seq(state.localVar, currStates.localVar), typVarMap),
                                translateExp(e, state, currStates))()
            val stmt1 = translateAssumeWithViperExpr(exp1, state, STmp, typVarMap)
            val exp2 = vpr.And(getInSetApp(Seq(state.localVar, currStates.localVar), typVarMap),
                                translateExp(UnaryExpr("!", e), state, currStates))()
            val stmt2 = translateAssumeWithViperExpr(exp2, state, tempFailedStates, typVarMap)
            val updateSFail = vpr.LocalVarAssign(failedStates.localVar,
                              getSetUnionApp(Seq(failedStates.localVar, tempFailedStates.localVar), typVarMap))()
            newStmts = Seq(havocSTmp, havocSFailTmp, stmt1, stmt2, updateSFail, updateProgStates)
            (newStmts, Seq.empty, Seq.empty)

        case as@AssignStmt(left, right) =>
            val leftVar = vpr.LocalVarDecl(left.name, translateType(SymbolChecker.allVars.get(left.name).get, typVarMap))()
            // Check whether the identifier on the left-hand side appears in the right-hand side
            if (as.IdsOnRHS.contains(left.name)) {
              val s0 = vpr.LocalVarDecl(s0VarName, state.typ)()
              val exp = vpr.EqCmp(translateExp(left, state, currStates), translateExp(right, s0, currStates))()
              val stmt = translateHavocVarHelper(leftVar, state, STmp, currStates, typVarMap, exp)
              newStmts = Seq(havocSTmp, stmt, updateProgStates)
            } else {
              val stmt1 = translateHavocVarHelper(leftVar, state, STmp, currStates, typVarMap)
              val exp = vpr.EqCmp(translateExp(left, state, currStates), translateExp(right, state, currStates))()
              val stmt2 = translateAssumeWithViperExpr(exp, state, STmp, typVarMap)
              newStmts = Seq(havocSTmp, stmt1, stmt2, updateProgStates)
            }
            (newStmts, Seq.empty, Seq.empty)

        case HavocStmt(id) =>
            val leftVar = vpr.LocalVarDecl(id.name, typVarMap.get(typeVar).get)()
            val stmt = translateHavocVarHelper(leftVar, state, STmp, currStates, typVarMap)
            newStmts = Seq(havocSTmp, stmt, updateProgStates)
            (newStmts, Seq.empty, Seq.empty)

        case IfElseStmt(cond, ifStmt, elseStmt) =>
            // Define new variables to hold the states in the if and else blocks respectively
            ifCounter = ifCounter + 1
            val ifBlockStates = vpr.LocalVarDecl(currStatesVarName + ifCounter, currStates.typ)()
            ifCounter = ifCounter + 1
            val elseBlockStates = vpr.LocalVarDecl(currStatesVarName + ifCounter, currStates.typ)()

            // Cond satisfied
            // Let ifBlockStates := S
            val assign1 = vpr.LocalVarAssign(ifBlockStates.localVar, currStates.localVar)()
            val assumeCond = translateStmt(AssumeStmt(cond), ifBlockStates)
            val ifBlock = translateStmt(ifStmt, ifBlockStates)

            // Cond not satisfied
            // Let elseBlockStates := S
            val assign2 = vpr.LocalVarAssign(elseBlockStates.localVar, currStates.localVar)()
            val assumeNotCond = translateStmt(AssumeStmt(UnaryExpr("!", cond)), elseBlockStates)
            val elseBlock = translateStmt(elseStmt, elseBlockStates)

            val updateSTmp = vpr.LocalVarAssign(STmp.localVar, getSetUnionApp(Seq(ifBlockStates.localVar, elseBlockStates.localVar), typVarMap))()

            newStmts = Seq(assign1) ++ assumeCond._1 ++ ifBlock._1 ++ Seq(assign2) ++ assumeNotCond._1 ++ elseBlock._1 ++ Seq(updateSTmp)
            newMethods = ifBlock._2 ++ elseBlock._2
            (newStmts, newMethods, Seq(ifBlockStates, elseBlockStates) ++ ifBlock._3 ++ elseBlock._3)

        case RequiresStmt(e) =>
            (Seq(vpr.Inhale(translateHyperAssertion(e, currStates, typVarMap))()), newMethods, Seq.empty)

        case EnsuresStmt(e) =>
            (Seq(vpr.Assert(translateHyperAssertion(e, currStates, typVarMap))()), newMethods, Seq.empty)

        case WhileLoopStmt(cond, body, inv) =>
            loopCounter = loopCounter + 1
            // Connect all invariants with && to form 1 invariant
            currLoopIndex = vpr.IntLit(0)()
            val I0 = getAllInvariants(inv, currStates, typVarMap)
            // Assert I(0)
            val assertI0 = vpr.Assert(I0)()
            // Verify invariant in a separate method
            newMethods = translateInvariantVerification(inv, cond, body, typVarMap)
            // Let currStates be a union of Sn's
            val havocCurrStates = havocSetMethodCall(currStates.localVar)
            val k = vpr.LocalVarDecl("k", vpr.Int)()
            val zero = vpr.IntLit(0)()
            val Sn = vpr.LocalVarDecl("Sn", getConcreteSetStateType(typVarMap))()
            currLoopIndex = k.localVar
            val unionStates = vpr.Exists(Seq(k, Sn), Seq.empty,
                                          vpr.And(vpr.GeCmp(k.localVar, zero)(),
                                              vpr.And(getInSetApp(Seq(state.localVar, Sn.localVar), typVarMap), getAllInvariants(inv, Sn, typVarMap))()
                                              )()
                                        )()
            val AssumeUnionStates = translateAssumeWithViperExpr(unionStates, state, currStates, typVarMap)
            // Translate assume !cond
            val notCond = translateStmt(AssumeStmt(UnaryExpr("!", cond)), currStates)
            newStmts = Seq(assertI0, havocCurrStates, AssumeUnionStates) ++ notCond._1
            (newStmts, newMethods, Seq.empty)
      }
    }


    def getAllInvariants(invs: Seq[Assertion], currStates: vpr.LocalVarDecl, typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.Exp = {
      if (invs.isEmpty) return vpr.BoolLit(true)()
      val translatedInvs = invs.map(i => translateHyperAssertion(i, currStates, typVarMap))
      translatedInvs.reduceLeft((e1, e2) => vpr.And(e1, e2)())
    }

    // Given a forall expression in the language: forall _s: State :: expr
    // Returns a forall expression in Viper: forall _s: State :: in_set(_s, currStates) ==> expr
    def translateHyperAssertion(inv: Assertion, currStates: vpr.LocalVarDecl, typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.Exp = {
          // Currently, inv has to be a ForAll expressions
          // Since inv is a hyperassertion, it must have state variables
          val stateVars = inv.assertVarDecls.filter(decl => decl.vType.isInstanceOf[StateType])
          val otherVars = inv.assertVarDecls.diff(stateVars)
          val vprStateVars = stateVars.map(s => translateAssertVarDecl(s, typVarMap))
          val vprOtherVars = otherVars.map(s =>  translateAssertVarDecl(s, typVarMap))
          val statesInSet: Seq[vpr.Exp] = vprStateVars.map(s => getInSetApp(Seq(s.localVar, currStates.localVar), typVarMap))
          val statesInSetAnd = statesInSet.reduceLeft((e1, e2) => vpr.And(e1, e2)())
          // In translateExp, a state variable is only explicitly used when an Id instance is detected,
          //  but hyperassertions do not contain Id instances, so it's ok to use null here
          val body = vpr.Implies(statesInSetAnd, translateExp(inv.body, null, currStates))()
          vpr.Forall(vprStateVars ++ vprOtherVars, Seq.empty, body)()
    }

    def translateInvariantVerification(inv: Seq[Assertion], loopGuard: Expr, body: CompositeStmt, typVarMap: Map[vpr.TypeVar, vpr.Type]): Seq[vpr.Method] = {
      val methodName = checkInvMethodName + loopCounter
      val currLoopIndexDecl = vpr.LocalVarDecl(currLoopIndexName + loopCounter, vpr.Int)()
      val inputStates = vpr.LocalVarDecl("S0", getConcreteSetStateType(typVarMap))()
      val outputStates = vpr.LocalVarDecl("SS", getConcreteSetStateType(typVarMap))()
      currLoopIndex = currLoopIndexDecl.localVar
      val In = getAllInvariants(inv, inputStates, typVarMap)
      currLoopIndex = vpr.Add(currLoopIndex, IntLit(1)())()
      val InPlus1 = getAllInvariants(inv, outputStates, typVarMap)

      val tmpStates = vpr.LocalVarDecl(tempStatesVarName, getConcreteSetStateType(typVarMap))()
      val assignToOutputStates = vpr.LocalVarAssign(outputStates.localVar, inputStates.localVar)()

      // Precondition 1: Loop index >= 1
      val pre1 = vpr.GeCmp(currLoopIndexDecl.localVar, IntLit(1)())()
      // Precondition 2: All program variables are different
      // (do so by assigning a distinct integer value to each of them)
      val allProgVarsInBody = body.allProgVars.map(v => vpr.LocalVarDecl(v._1, translateType(v._2, typVarMap))()).toList
      val allProgVarsWithValues = allProgVarsInBody.map(v => vpr.EqCmp(v.localVar, vpr.IntLit(allProgVarsInBody.indexOf(v))())())
      val pre2: Seq[vpr.Exp] = if (allProgVarsWithValues.isEmpty) Seq.empty else Seq(allProgVarsWithValues.reduce((e1: vpr.Exp, e2: vpr.Exp) => vpr.And(e1, e2)()))

      // Assume loop guard
      val assumeLoopGuard = translateStmt(AssumeStmt(loopGuard), outputStates)
      // Translation of the loop body
      val loopBody = translateStmt(body, outputStates)
      val methodBody = Seq(assignToOutputStates) ++ assumeLoopGuard._1 ++ loopBody._1

      val thisMethod = vpr.Method(methodName,
          Seq(currLoopIndexDecl, inputStates) ++ allProgVarsInBody,  // args
          Seq(outputStates),  // return values
          Seq(pre1, In) ++ pre2,  // pre
          Seq(InPlus1),  // post
          Some(Seqn(methodBody, Seq(tmpStates) ++ loopBody._3.diff(allProgVarsInBody))())    // body
        )()
      Seq(thisMethod) ++ loopBody._2
    }

    def translateExp(e: Expr, state: vpr.LocalVarDecl, currStates: vpr.LocalVarDecl): vpr.Exp = {
      val typVarMap = if (state != null) state.typ.asInstanceOf[vpr.DomainType].partialTypVarsMap
                      else Map(typeVar -> vpr.Int)
      e match {
        case Id(name) =>
          // Any reference to a var is translated to get(state, var)
          val id = vpr.LocalVar(name, translateType(SymbolChecker.allVars.getOrElse(name, null)))()
          getGetApp(Seq(state.localVar, id), state.typ.asInstanceOf[vpr.DomainType].partialTypVarsMap)
        case Num(value) => vpr.IntLit(value)()
        case BoolLit(value) => vpr.BoolLit(value)()
        case BinaryExpr(left, op, right) =>
          op match {
            case "+" => vpr.Add(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "-" => vpr.Sub(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "*" => vpr.Mul(translateExp(left, state, currStates), translateExp(right, state, currStates))()
            case "/" => vpr.Div(translateExp(left, state, currStates), translateExp(right, state, currStates))()
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
        case a@Assertion(quantifier, vars, body) =>
          val variables = vars.map(v => translateAssertVarDecl(v, typVarMap))
          if (quantifier == "forall") {
            if (a.hasStateVar) translateHyperAssertion(a, currStates, typVarMap)
            else vpr.Forall(variables, Seq.empty, translateExp(body, state, currStates))()
          }
          else if (quantifier == "exists") {
            vpr.Exists(variables, Seq.empty, translateExp(body, state, currStates))()
          }
          else throw UnknownException("Unexpected quantifier " + quantifier)
        case ImpliesExpr(left, right) =>
          vpr.Implies(translateExp(left, state, currStates), translateExp(right, state, currStates))()
        case GetValExpr(s, id) =>
          val stateVar = vpr.LocalVarDecl(s.name, getConcreteStateType(typVarMap))()
          translateExp(id, stateVar, currStates)
        // case AssertVarDecl(vName, vType) => This is translated in a separate method below, as vpr.LocalVarDecl is of type Stmt
        // TODO:
//        case StateExistsExpr(state) =>
        case LoopIndex() => currLoopIndex
        case _ =>
          throw UnknownException("Unexpected expression " + e)
      }
    }

  def translateAssertVarDecl(decl: AssertVarDecl, typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.LocalVarDecl = {
    vpr.LocalVarDecl(decl.vName.name, translateType(decl.vType, typVarMap))()
  }

  // This returns a Viper assume statement that expresses the following:
  // assume forall stateVar :: in_set(stateVar, tmpStates) ==> (exists s0 :: in_set(s0, currStates) && equal_on_everything_except(s0, stateVar, leftVar) && extraExp)
  def translateHavocVarHelper(leftVar: vpr.LocalVarDecl, stateVar: vpr.LocalVarDecl, tmpStates: vpr.LocalVarDecl,
                              currStates: vpr.LocalVarDecl, typVarMap: Map[vpr.TypeVar, vpr.Type], extraExp: vpr.Exp = null)
                                : vpr.Inhale = {
    val s0 = vpr.LocalVarDecl(s0VarName, stateVar.typ)()
    var itemsInExistsExpr: Seq[vpr.Exp] = Seq(getInSetApp(Seq(s0.localVar, currStates.localVar), typVarMap),
                                getEqualExceptApp(Seq(s0.localVar, stateVar.localVar, leftVar.localVar), typVarMap))
    if (extraExp != null) itemsInExistsExpr = itemsInExistsExpr :+ extraExp
    val existsExpr = vpr.Exists(Seq(s0), Seq.empty, itemsInExistsExpr.reduceLeft((e1, e2) => vpr.And(e1, e2)()))()
    translateAssumeWithViperExpr(existsExpr, stateVar, tmpStates, typVarMap)
  }

  // This returns a Viper assume statement of the form "assume forall stateVar: State[T] :: in_set(stateVar, pStates) => e"
  // T is determined by the typVarMap(T -> someType)
  def translateAssumeWithViperExpr(e: vpr.Exp, stateVar: vpr.LocalVarDecl, states: vpr.LocalVarDecl, typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.Inhale = {
    vpr.Inhale(
      vpr.Forall(
        Seq(stateVar),
        Seq.empty,
        vpr.Implies(
          getInSetApp(Seq(stateVar.localVar, states.localVar), typVarMap),
          e
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
