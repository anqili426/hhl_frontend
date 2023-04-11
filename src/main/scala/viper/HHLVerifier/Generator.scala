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
  val stateType = vpr.DomainType(stateDomainName, Map(typeVar -> typeVar))(Seq(typeVar))
  val setStateType = vpr.DomainType(setStateDomainName, Map(typeVar -> typeVar))(Seq(typeVar))
  val TtoIntMap = Map(typeVar -> vpr.Int)

  val sVar = vpr.LocalVarDecl("s", stateType)()
  val s1Var = vpr.LocalVarDecl("s1", stateType)()
  val s2Var = vpr.LocalVarDecl("s2", stateType)()
  val xVar = vpr.LocalVarDecl("x", typeVar)()
  val yVar = vpr.LocalVarDecl("y", typeVar)()
  val SVar = vpr.LocalVarDecl("S", setStateType)()
  val S1Var = vpr.LocalVarDecl("S1", setStateType)()
  val S2Var = vpr.LocalVarDecl("S2", setStateType)()

  val setStateWithIntType = getConcreteSetStateType(TtoIntMap)
  val sVarInt = vpr.LocalVarDecl("s", getConcreteStateType(TtoIntMap))()


  val pSetStateVarName = "S"
  val pTmpSetStateVarName = "S_temp"
  val pFailSetStateVarName = "S_fail"
  val pTmpFailSetStateVarName = "S_fail_temp"
  val pSetStateVar = vpr.LocalVarDecl(pSetStateVarName, getConcreteSetStateType(TtoIntMap))()
  val pTmpSetStateVar = vpr.LocalVarDecl(pTmpSetStateVarName, getConcreteSetStateType(TtoIntMap))()
  val pFailSetStateVar = vpr.LocalVarDecl(pFailSetStateVarName, getConcreteSetStateType(TtoIntMap))()
  val pFailTmpSetStateVar = vpr.LocalVarDecl(pTmpFailSetStateVarName, getConcreteSetStateType(TtoIntMap))()

  val havocSetMethodName = "havocSet"


  def generate(input: HHLProgram): vpr.Program = {
    var domains: Seq[vpr.Domain] = Seq.empty
    var fields: Seq[vpr.Field] = Seq.empty
    var functions: Seq[vpr.Function] = Seq.empty
    var predicates: Seq[vpr.Predicate] = Seq.empty
    var methods: Seq[vpr.Method] = Seq.empty
    var extensions: Seq[vpr.ExtensionMember] = Seq.empty

    val preamble = generatePreamble()
    domains = domains ++ preamble._1
    methods = methods ++ preamble._2 ++ translateProgram(input)
    val p = vpr.Program(domains, fields, functions, predicates, methods, extensions)()
    p
  }

  def translateProgram(input: HHLProgram): Seq[vpr.Method] = {
      val translatedContent = translateStmt(input.content, Seq.empty, Seq.empty)
      var localVars = Seq(pSetStateVar, pTmpSetStateVar, pFailTmpSetStateVar, pFailSetStateVar)
      localVars = localVars ++ Parser.allVars.map(kv => vpr.LocalVarDecl(kv._1, translateType(kv._2))())
      // TODO: also need to assume that variables are not the same!
      val mainMethod = vpr.Method("main", Seq.empty, Seq.empty, Seq.empty, Seq.empty,
                                  Some(vpr.Seqn(translatedContent._1, localVars)()))()
      mainMethod +: translatedContent._2
  }

    def translateStmt(stmt: Stmt, translatedStmt: Seq[vpr.Stmt], translatedMethods: Seq[vpr.Method]): (Seq[vpr.Stmt], Seq[vpr.Method]) = {
      val havocSTmp = havocSetMethodCall(pTmpSetStateVar.localVar)
      val updateS = vpr.LocalVarAssign(pSetStateVar.localVar, pTmpSetStateVar.localVar)()

      stmt match {
        case CompositeStmt(stmts) =>
          // Translate each statement in the sequence
          var tmpRes = (translatedStmt, translatedMethods)
          for (s <- stmts) {
            tmpRes = translateStmt(s, tmpRes._1, tmpRes._2)
          }
          tmpRes
        case AssumeStmt(e) =>
          val res = translateAssumeExpHelper(e)
          (translatedStmt :+ havocSTmp :+ res :+ updateS , translatedMethods)
        case AssertStmt(e) =>
          val havocSFailTmp = havocSetMethodCall(pFailTmpSetStateVar.localVar)
          val updateSFail = vpr.LocalVarAssign(pFailSetStateVar.localVar, pFailTmpSetStateVar.localVar)()
          val tmpRes = Seq(translateAssumeExpHelper(e), translateAssumeExpHelper(UnaryExpr("!",e)))
          val resStmt = ((translatedStmt :+ havocSTmp :+ havocSFailTmp) ++ tmpRes) :+ updateS :+ updateSFail
          (resStmt, translatedMethods)
          // Assign
          // Havoc
          // If Else
          // While -- Need to define assertion language
        case _ =>
          (translatedStmt, translatedMethods)
      }
    }

    def translateExp(e: Expr): vpr.Exp = {
      e match {
        case Id(name) => vpr.LocalVar(name, translateType(Parser.allVars.getOrElse(name, null)))()
        case Num(value) => vpr.IntLit(value)()
        case Bool(value) => vpr.BoolLit(value)()
        case BinaryExpr(left, op, right) =>
          op match {
            case "+" => vpr.Add(translateExp(left), translateExp(right))()
            case "-" => vpr.Sub(translateExp(left), translateExp(right))()
            case "*" => vpr.Mul(translateExp(left), translateExp(right))()
            case "/" => vpr.Div(translateExp(left), translateExp(right))()
            case "&&" => vpr.And(translateExp(left), translateExp(right))()
            case "||" => vpr.Or(translateExp(left), translateExp(right))()
            case "==" => vpr.EqCmp(translateExp(left), translateExp(right))()
            case "!=" => vpr.NeCmp(translateExp(left), translateExp(right))()
            case ">" => vpr.GtCmp(translateExp(left), translateExp(right))()
            case ">=" => vpr.GeCmp(translateExp(left), translateExp(right))()
            case "<" => vpr.LtCmp(translateExp(left), translateExp(right))()
            case "<=" => vpr.LeCmp(translateExp(left), translateExp(right))()
          }
        case UnaryExpr(op, e) =>
          op match {
            case "!" => vpr.Not(translateExp(e))()
            case "-" => vpr.Minus(translateExp(e))()
          }
        // case Havoc() =>  No need to translate anything
      }
    }

    def translateAssumeExpHelper(e: Expr): vpr.Assume = {
      vpr.Assume(
        vpr.Forall(
          Seq(sVarInt),
          Seq.empty,
          vpr.Implies(
            getInSetApp(Seq(sVarInt.localVar, pTmpSetStateVar.localVar), TtoIntMap),
            vpr.And(
              getInSetApp(Seq(sVarInt.localVar, pSetStateVar.localVar), TtoIntMap),
              translateExp(e)
            )()
          )()
        )()
      )()
    }

    def translateType(typName: String): vpr.Type = {
        typName match {
          case "Int" => vpr.Int
          case "Bool" => vpr.Bool
        }
    }

  def generatePreamble(): (Seq[vpr.Domain], Seq[vpr.Method]) = {
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

    val SS = vpr.LocalVarDecl("SS", getConcreteSetStateType(TtoIntMap))()
    val havocSetMethod = vpr.Method(havocSetMethodName, Seq.empty, Seq(SS), Seq.empty, Seq.empty, Option.empty)()

    (Seq(stateDomain, setStateDomain), Seq(havocSetMethod))

  }

  def getConcreteSetStateType(typVarMap: Map[TypeVar, Type]): vpr.Type = {
    vpr.DomainType(setStateDomainName, typVarMap)(Seq(typeVar))
  }

  def getConcreteStateType(typVarMap: Map[TypeVar, Type]): vpr.Type = {
    vpr.DomainType(stateDomainName, typVarMap)(Seq(typeVar))
  }

  def havocSetMethodCall(set: vpr.LocalVar): vpr.MethodCall = {
    vpr.MethodCall(havocSetMethodName, Seq.empty, Seq(set))(pos = vpr.NoPosition, info = vpr.NoInfo, errT = vpr.NoTrafos)
  }

  def getInSetApp(args: Seq[vpr.Exp], typVarMap: Map[TypeVar, Type]): vpr.DomainFuncApp = {
    getDomainFuncApp(inSetFuncName, args, setStateDomainName, vpr.Bool, typVarMap)
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
