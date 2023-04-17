package viper.HHLVerifier
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

  val typeVar = vpr.TypeVar("T")
  val stateType = getConcreteStateType(Map.empty)   // Type State[T]
  val setStateType = getConcreteSetStateType(Map.empty) // Type SetState[T]

  val sVarName = "s"
  val s0VarName = "s0"
  val currStatesVarName = "S"
  val tempStatesVarName = "S_temp"
  val failedStatesVarName = "S_fail"
  val tempFailedStatesVarName = "S_fail_temp"
  var failedStates = vpr.LocalVarDecl(failedStatesVarName, setStateType)()
  var tempFailedStates = vpr.LocalVarDecl(tempFailedStatesVarName, setStateType)()

  var extraVars: List[vpr.LocalVarDecl] = List.empty // Extra variables added to the program during translation

  var counter = 0

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

      val localVars = Seq(currStates, tempStates, tempFailedStates, failedStates) ++ extraVars
      // TODO: Also need to assume that variables are not the same!
      val state = vpr.LocalVarDecl(sVarName, getConcreteStateType(typVarMap))()
      // The following statement assumes that S_fail is empty
      val assumeSFailEmpty = vpr.Assume(vpr.Forall(
                                            Seq(state),
                                            Seq.empty,
                                            vpr.Not(
                                              getInSetApp(Seq(state.localVar, failedStates.localVar), typVarMap)
                                            )()
                                          )()
                                        )()
      val methodBody = assumeSFailEmpty +: translatedContent._1
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
    def translateStmt(stmt: Stmt, currStates: vpr.LocalVarDecl): (Seq[vpr.Stmt], Seq[vpr.Method]) = {
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

      stmt match {
        case CompositeStmt(stmts) =>
          // Translate each statement in the sequence
          var resStmts: Seq[vpr.Stmt] = Seq.empty
          var resMethods: Seq[vpr.Method] = Seq.empty
          var tmpRes = (resStmts, resMethods)
          for (s <- stmts) {
            tmpRes = translateStmt(s, currStates)
            resStmts = resStmts ++ tmpRes._1
            resMethods = resMethods ++ tmpRes._2
          }
          return (resStmts, resMethods)

        case PVarDecl(name, typ) =>
          val thisVar = vpr.LocalVarDecl(name.name, translateType(typ))()
          extraVars = extraVars :+ thisVar
          return (Seq.empty, Seq.empty)
        case AssumeStmt(e) =>
          val exp = vpr.And(getInSetApp(Seq(state.localVar, currStates.localVar), typVarMap),
                                        translateExp(e, state))()
          newStmts = Seq(translateAssumeWithViperExpr(exp, state, STmp, typVarMap))

        case AssertStmt(e) =>
            val havocSFailTmp = havocSetMethodCall(tempFailedStates.localVar)
            val exp1 = vpr.And(getInSetApp(Seq(state.localVar, currStates.localVar), typVarMap),
                                translateExp(e, state))()
            val stmt1 = translateAssumeWithViperExpr(exp1, state, STmp, typVarMap)
            val exp2 = vpr.And(getInSetApp(Seq(state.localVar, currStates.localVar), typVarMap),
                                translateExp(UnaryExpr("!", e), state))()
            val stmt2 = translateAssumeWithViperExpr(exp2, state, tempFailedStates, typVarMap)
            val updateSFail = vpr.LocalVarAssign(failedStates.localVar,
                              getSetUnionApp(Seq(failedStates.localVar, tempFailedStates.localVar), typVarMap))()
            newStmts = Seq(havocSFailTmp, stmt1, stmt2, updateSFail)

        case AssignStmt(left, right) =>
            val leftVar = vpr.LocalVarDecl(left.name, typVarMap.get(typeVar).get)()
            val stmt1 = translateHavocVarHelper(leftVar, state, STmp, currStates, typVarMap)
            val exp = vpr.EqCmp(translateExp(left, state), translateExp(right, state))()
            val stmt2 = translateAssumeWithViperExpr(exp, state, STmp, typVarMap)
            newStmts = Seq(stmt1, stmt2)

        case HavocStmt(id) =>
          val leftVar = vpr.LocalVarDecl(id.name, typVarMap.get(typeVar).get)()
          val stmt = translateHavocVarHelper(leftVar, state, STmp, currStates, typVarMap)
          newStmts = Seq(stmt)

        case IfElseStmt(cond, ifStmt, elseStmt) =>
          // Define new variables to hold the states in the if and else blocks respectively
          counter = counter + 1
          val ifBlockStates = vpr.LocalVarDecl(currStatesVarName + counter, currStates.typ)()
          counter = counter + 1
          val elseBlockStates = vpr.LocalVarDecl(currStatesVarName + counter, currStates.typ)()
          extraVars = extraVars :+ ifBlockStates :+ elseBlockStates

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
//        TODO: case WhileLoopStmt(cond, body) =>
      }
      // Translation of S := S_temp
      val updateProgStates = vpr.LocalVarAssign(currStates.localVar, STmp.localVar)()
      newStmts = (havocSTmp +: newStmts) :+ updateProgStates
      (newStmts, newMethods)
    }

    def translateExp(e: Expr, state: vpr.LocalVarDecl): vpr.Exp = {
      e match {
        case Id(name) =>
          // Any reference to a var is translated to get(state, var)
          val id = vpr.LocalVar(name, translateType(SymbolChecker.allVars.getOrElse(name, null)))()
          getGetApp(Seq(state.localVar, id), state.typ.asInstanceOf[vpr.DomainType].partialTypVarsMap)
        case Num(value) => vpr.IntLit(value)()
        case BoolLit(value) => vpr.BoolLit(value)()
        case BinaryExpr(left, op, right) =>
          op match {
            case "+" => vpr.Add(translateExp(left, state), translateExp(right, state))()
            case "-" => vpr.Sub(translateExp(left, state), translateExp(right, state))()
            case "*" => vpr.Mul(translateExp(left, state), translateExp(right, state))()
            case "/" => vpr.Div(translateExp(left, state), translateExp(right, state))()
            case "&&" => vpr.And(translateExp(left, state), translateExp(right, state))()
            case "||" => vpr.Or(translateExp(left, state), translateExp(right, state))()
            case "==" => vpr.EqCmp(translateExp(left, state), translateExp(right, state))()
            case "!=" => vpr.NeCmp(translateExp(left, state), translateExp(right, state))()
            case ">" => vpr.GtCmp(translateExp(left, state), translateExp(right, state))()
            case ">=" => vpr.GeCmp(translateExp(left, state), translateExp(right, state))()
            case "<" => vpr.LtCmp(translateExp(left, state), translateExp(right, state))()
            case "<=" => vpr.LeCmp(translateExp(left, state), translateExp(right, state))()
          }
        case UnaryExpr(op, e) =>
          op match {
            case "!" => vpr.Not(translateExp(e, state))()
            case "-" => vpr.Minus(translateExp(e, state))()
          }
        case av@AssertVar(name) =>
          vpr.LocalVar(name, translateType(av.typ))()
        case ForAllExpr(vars, body) =>
          val variables = vars.map(v => translateAssertVarDecl(v))
          vpr.Forall(variables, Seq.empty, translateExp(body, state))()
        case ExistsExpr(vars, body) =>
          val variables = vars.map(v => translateAssertVarDecl(v))
          vpr.Exists(variables, Seq.empty, translateExp(body, state))()
        case ImpliesExpr(left, right) =>
          vpr.Implies(translateExp(left, state), translateExp(right, state))()
        // case AssertVarDecl(name, typ) => TODO: raise error here
      }
    }

  def translateAssertVarDecl(decl: AssertVarDecl): vpr.LocalVarDecl = {
    vpr.LocalVarDecl(decl.vName.name, translateType(decl.vType))()
  }

  // This returns a Viper assume statement that expresses the following:
  // assume forall stateVar :: in_set(stateVar, tmpStates) ==> (exists s0 :: in_set(s0, currStates) && equal_on_everything_except(s0, stateVar, leftVar))
  def translateHavocVarHelper(leftVar: vpr.LocalVarDecl, stateVar: vpr.LocalVarDecl, tmpStates: vpr.LocalVarDecl,
                              currStates: vpr.LocalVarDecl, typVarMap: Map[vpr.TypeVar, vpr.Type])
                                : vpr.Assume = {
    val s0 = vpr.LocalVarDecl(s0VarName, stateVar.typ)()
    val existsExpr = vpr.Exists(Seq(s0), Seq.empty,
                                vpr.And(getInSetApp(Seq(s0.localVar, currStates.localVar), typVarMap),
                                        getEqualExceptApp(Seq(s0.localVar, stateVar.localVar, leftVar.localVar), typVarMap)
                                        )()
                                )()
    translateAssumeWithViperExpr(existsExpr, stateVar, tmpStates, typVarMap)
  }

  // This returns a Viper assume statement of the form "assume forall stateVar: State[T] :: in_set(stateVar, pStates) => e"
  // T is determined by the typVarMap(T -> someType)
  def translateAssumeWithViperExpr(e: vpr.Exp, stateVar: vpr.LocalVarDecl, states: vpr.LocalVarDecl, typVarMap: Map[vpr.TypeVar, vpr.Type]): vpr.Assume = {
    vpr.Assume(
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

    def translateType(typ: Type): vpr.Type = {
        typ match {
          case IntType() => vpr.Int
          case BoolType() => vpr.Bool
          case null => println("null type")
            vpr.Int
          // TODO: state type!!
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
            vpr.Forall(
              Seq(yVar),
              Seq.empty,
              vpr.Implies(getEqualExceptApp(Seq(s1Var.localVar, s2Var.localVar, xVar.localVar), TToTMap),
                vpr.Implies(vpr.NeCmp(xVar.localVar, yVar.localVar)(),
                  vpr.EqCmp(getGetApp(Seq(s1Var.localVar, xVar.localVar)),
                    getGetApp(Seq(s2Var.localVar, xVar.localVar))
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

  def getInSetApp(args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type] = Map.empty): vpr.DomainFuncApp = {
    getDomainFuncApp(inSetFuncName, args, vpr.Bool, typVarMap)
  }

  def getSetUnionApp(args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type] = Map(typeVar -> typeVar)): vpr.DomainFuncApp = {
    getDomainFuncApp(setUnionFuncName, args, getConcreteSetStateType(typVarMap), typVarMap)
  }

  def getEqualExceptApp(args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type] = Map.empty): vpr.DomainFuncApp = {
    getDomainFuncApp(equalFuncName, args, vpr.Bool, typVarMap)
  }

  def getGetApp(args: Seq[vpr.Exp], typVarMap: Map[vpr.TypeVar, vpr.Type] = Map.empty): vpr.DomainFuncApp = {
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
