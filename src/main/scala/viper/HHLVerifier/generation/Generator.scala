package viper.HHLVerifier.generation

import viper.HHLVerifier.ast._
import viper.HHLVerifier.generation.Generator.InvariantTracking.InvariantDebugInfo
import viper.HHLVerifier.typing._
import viper.HHLVerifier.management._
import viper.silver.ast.{Info, NoInfo}
import viper.silver.{ast => vpr}

/** Documentation of Error Handling
 *
 * For all errors which do not include invariants:
 * - There is a specific error generator class, which captures the faulty expression, wraps it into a nice error
 *   encodes it into the hypra encoding
 *
 * For all errors which include invariants
 * - Invariants are transformed multiple times in the process. Therefore, we need to track which transformed invariant
 *   belongs to which original one. This is achieved by using the invariant tracking object.
 * - Every invariant is added to the tracker when it is first discovered
 * - Additionally, when an invariant is transformed by a quantifier removal, the removed quantifier count is updated to
 *   allow to inform the user about the state of the expression which caused the error
 * */

// TODO: Check if the splitting in inv and decr is correct

object Generator {
  // Frequently used constants
  // State domain
  val stateDomainName = "State"
  val equalFuncName = "equal_on_everything_except"
  val getFuncName = "get"

  // SetState domain
  val setStateDomainName = "SetState"
  val inSetFuncName = "in_set"
  val inSetForAllFuncName = "in_set_forall"
  val inSetForAllLimitedFuncName = "in_set_forall_limited"
  val inSetExistsFuncName = "in_set_exists"
  val inSetExistsLimitedFuncName = "in_set_exists_limited"
  val setUnionFuncName = "set_union"

  val sVarName = "_s"
  val s0VarName = "_s0"
  val s1VarName = "_s1"
  val s2VarName = "_s2"
  val currStatesVarName = "S"
  val tempStatesVarName = "S_temp"
  val failedStatesVarName = "S_fail"
  val tempFailedStatesVarName = "S_fail_temp"

  val havocSetMethodName = "havocSet"
  val havocIntMethodName = "havocInt"
  val checkInvMethodName = "check_inv"

  var ifCounter = 0
  var loopCounter = 0
  var alignCounter = 0
  var stateVarCounter = 0
  var currLoopIndex: vpr.Exp = null
  var currLoopIndexName = "$n"

  // Logical variables needed in the encodings
  // The identifier of each logical variable starts with two underscores
  // This guarantees no name clash between logical variables and any variables written by users
  val nonDetBoolName = "__check_inv_cond" // Used during inline verification of invariants
  val checkSyncCondName = "__use_sync_rule"
  val kVarName = "__k"
  val progVarName = "__progVar" // Used for auto-framing
  val tVarName = "__t"  // Used when there is a decreases clause
  val isIfBlockVarName = "__isIfBlock" // Flag used when translating alignment

  val hintWrapperSuffix = "_wrapper"

  var allMethods: Seq[vpr.Method] = Seq.empty // NO NEED
  var allFuncs: Seq[vpr.Function] = Seq.empty
  var allDomains: Seq[vpr.Domain] = Seq.empty

  var verifierOption = 0 // 0: forall 1: exists 2: both
  var inline = false  // true: verification of the loop invariant will be inline
  var forAllFrame = true // true: forall automatic framing is enabled
  var existsFrame = false // true: forall automatic framing is enabled
  var autoSelectRules = false // true: selection of loop rules is automatic

  // This variable is used when translating declarations of proof variables
  // When set to true, use an alias for the proof variable referred to by currProofVar
  // The alias is different from its declared identifier
  var useAliasForProofVar = false
  var currProofVarName = ""

  // These variables are used when translating a postcondition of a method
  var containsHints = false // true if the postcondition contains any hints
  var removeHints = false // true if we need to remove the hints from the postconditions

  // Viper int literals
  val one = vpr.IntLit(1)()
  val zero = vpr.IntLit(0)()

  // Vpr bool literals
  val trueLit = vpr.BoolLit(true)()
  val falseLit = vpr.BoolLit(false)()

  // This is true when a hyper-assertion should be translated with triggers
  // Should be set to true before translating a method precondition and invariant I(n)
  // And should be set back to false immediately after
  var needTriggers = false

  // This is true when we want to translate a method precondition with the parameters replaced with arguments
  var useParamsToArgsMap = false
  var currParamsToArgsMap: Map[String, String] = Map.empty

  var currMethod: Method = null
  var postIsTopExists = false
  var syncTotWarningPrinted = false
  var isPostcondition = false

  // var useAliasForState = false
  var stateAliasPrefix = "_"
  val checkSyncCondMethodName = "check_sync_cond"
  val checkExistsRuleCond1MethodName = "check_exists_cond1"
  val checkExistsRuleCond2MethodName = "check_exists_cond2"
  var stateRemoved = ""

  /** tracks information necessary to debug invariants */
  object InvariantTracking {
    class InvariantDebugInfo(val inv: Expr) {
      var quantifiersRemoved = 0

      def incrRemovedQuantifier(): Unit = { quantifiersRemoved += 1 }
      def decrRemovedQuantifier(): Unit = { quantifiersRemoved += 1 }
    }
    class InvariantWithID(val inv: Expr, val id: Int)

    private var counter = 0;
    private var tracker: Map[Int, InvariantDebugInfo] = Map.empty

    def insert(el: InvariantDebugInfo): Int = {
      counter += 1
      tracker = tracker + (counter -> el)
      counter
    }
    def get(key: Int): InvariantDebugInfo = tracker.get(key).get
    def remove(key: Int): Unit = tracker.removed(key)
  }

  // Main generate method
  // - saves program source and used types
  // - creates all aspects necessary for generating a vpr program
  // - creates preamble containing all necessary base functions
  // - translates actual program
  def generate(input: HHLProgram, source: String): vpr.Program = {
    val fields: Seq[vpr.Field] = Seq.empty
    val predicates: Seq[vpr.Predicate] = Seq.empty
    val extensions: Seq[vpr.ExtensionMember] = Seq.empty

    val preamble = generatePreamble()
    allDomains = allDomains ++ preamble._1
    allMethods = allMethods ++ preamble._2
    translateProgram(input)
    val p = vpr.Program(allDomains, fields, allFuncs, predicates, allMethods, extensions)()
    p
  }

  // Generate a viper program with the following
  // 1. A method that checks if I implies low(b)
  //    pre: I
  //    post: low(b)
  //    body: empty
  // 2. The method should contain domain declarations

  def reset(): Unit = {
    allDomains = Seq.empty
    allMethods = Seq.empty
    allFuncs = Seq.empty
  }

  // Translate every method individually
  def translateProgram(input: HHLProgram): Unit = input.content.map(translateMethod)

  // Translate a method
  // -
  def translateMethod(method: Method): Unit = {
    currMethod = method
    // Declaring states
    val inputStates = SetState.localVarDecl("S0")
    val outputStates = SetState.localVarDecl(currStatesVarName)
    val tempStates = SetState.localVarDecl(tempStatesVarName)
    val outputFailureStates = SetState.localVarDecl(failedStatesVarName)
    val tempFailedStates = SetState.localVarDecl(tempFailedStatesVarName)
    val state = State.localVarDecl(sVarName)

    // The following statement assumes that S_fail is empty
    val assumeSFailEmpty = vpr.Inhale(vpr.Forall(
      Seq(state),
      Seq.empty,
      vpr.Not(SetState.getInSetApp(Seq(state.localVar, outputFailureStates.localVar)))()
    )())()

    // The following statement assumes in_set_forall == in_set_exists for all states in S
    val inSetEq = inhaleInSetEqStmt(state, inputStates.localVar)
    val inSetFailEq = inhaleInSetEqStmt(state, outputFailureStates.localVar)

    // Arguments of the input method
    val args = method.params.map(id => vpr.LocalVarDecl(id.name, id.typ match {
      case _: StateType => translateType(id.typ)
      case _: StmtBlockType => translateType(id.typ)
      case _: UnknownType => translateType(id.typ)
      case _ => vpr.Int
    })())
    val translatedArgs = args :+ inputStates

    // Return variables of the input method
    val ret = method.res.map(id => vpr.LocalVarDecl(id.name, id.typ match {
      case _: StateType => translateType(id.typ)
      case _: StmtBlockType => translateType(id.typ)
      case _: UnknownType => translateType(id.typ)
      case _ => vpr.Int
    })())
    val retVars = ret.map(r => r.localVar)

    // Forming the preconditions
    val argsWithValues = args.map(v => vpr.EqCmp(v.localVar, vpr.IntLit(args.indexOf(v))())())
    val preAboutArgs = if (argsWithValues.isEmpty) Seq.empty else Seq(argsWithValues.reduce((e1: vpr.Exp, e2: vpr.Exp) => vpr.And(e1, e2)()))
    val normalizedPres = method.pre.map(p => Normalizer.normalize(p, false))
    normalizedPres.foreach(p => Normalizer.detQuantifier(p, false))
    val pres = normalizedPres.map(p => getAssertionWithTriggers(p, inputStates.localVar, null)) ++ preAboutArgs

    // Forming the postconditions
    isPostcondition = true
    // postconditions and debug info
    val posts = method.post.map { exp =>
      val normalizedPost = Normalizer.normalize(exp, negate = false)
      Normalizer.detQuantifier(normalizedPost, underForAll = false)

      translateExp(normalizedPost, null, outputStates.localVar, outputFailureStates.localVar, info =
        new Logger(VerificationErrors.Postcondition(exp), Logger.ERR)
          .addTitle("Verification Error")
          .addOffset((exp.offsetLeft, exp.offsetRight))
          .toAnnotationInfo())
    }
    isPostcondition = false

    /* Method body contains the following
    *  Local variable declaration (program variables + auxiliary variables of type SetState + isIfBlock)
    *  Assume all program variables used in the method are different
    *  Assignment S := S0
    *  Assumption that S_fail is empty
    *  The translation of the input method body
    */

    // Let S := S0
    val currStatesAssignment = vpr.LocalVarAssign(outputStates.localVar, inputStates.localVar)()
    val translatedContent = translateStmt(method.body, outputStates.localVar, outputFailureStates.localVar)

    // Aux variables of type Int generated during translation of the method body
    val auxiliaryVars = translatedContent._2.filter(el => el.typ == vpr.Int)
    // println("Auxilary Variables: " + auxiliaryVars)
    val auxiliaryVarDecls = auxiliaryVars.map(v => vpr.LocalVarDecl(v.name, v.typ)())

    // Assume that all program variables + return variables are different by assigning a distinct value to each of them
    // Program variables that are not method arguments or return values
    val progVars = method.body.allProgVars.filter(v => !method.paramsMap.keySet.contains(v._1) && !method.resMap.keySet.contains(v._1))
    val progVarsAsIds = progVars.map { keyVal =>
      val id = Id(keyVal._1)
      id.typ = keyVal._2
      id
    }.toSeq

    // Currently, we only support program variables of type Integer, so pick them out
    val translatedProgVars = progVars.map(v => getVprVar(v._1)).toSeq
    // println("Translated Prog Vars: " + translatedProgVars)
    val allVarsToAssign = translatedProgVars ++ auxiliaryVars ++ retVars
    val assignToVars = allVarsToAssign.map(v => vpr.LocalVarAssign(v, vpr.IntLit(allVarsToAssign.indexOf(v) + args.length)())())
    // println("All vars to assign: " + assignToVars)

    val progVarDecls = translateMethodVariables(progVarsAsIds)
    val nonIntAuxVars = Seq(tempStates, tempFailedStates) ++ translatedContent._2.diff(auxiliaryVars).map(v => vpr.LocalVarDecl(v.name, v.typ)())
    val localVars = progVarDecls ++ auxiliaryVarDecls ++ nonIntAuxVars
    // println("Local Vars " + localVars)

    val methodBody = Seq(currStatesAssignment, assumeSFailEmpty) ++ inSetEq ++ inSetFailEq ++ assignToVars ++ translatedContent._1
    val thisMethod = vpr.Method(method.mName, translatedArgs, ret ++ Seq(outputStates, outputFailureStates), pres, posts, Some(vpr.Seqn(methodBody, localVars)()))() // UPDATED
    allMethods = allMethods :+ thisMethod
    postIsTopExists = false
  }

  /*
  * The following method returns:
  * 1. the translated statement(s)
  * 2. new auxiliary variables added during translation (happens when translating an if-else block)
  */
  def translateStmt(stmt: Stmt, currStates: vpr.LocalVar, currFailureStates: vpr.LocalVar, isAutoSelected: Boolean = false): (Seq[vpr.Stmt], Seq[vpr.LocalVar]) = {
    // A set of states
    val STmp = SetState.localVar(tempStatesVarName) // val STmp = vpr.LocalVar(tempStatesVarName, currStates.typ)()
    // A state
    val state = State.localVar(sVarName) // vpr.LocalVar(sVarName, getConcreteStateType(typVarMap))()
    val stateDecl = State.localVarDecl(sVarName)
    // Results
    var existsNewStmts: Seq[vpr.Stmt] = Seq.empty
    var forallNewStmts: Seq[vpr.Stmt] = Seq.empty
    var newStmts: Seq[vpr.Stmt] = Seq.empty
    var newMethods: Seq[vpr.Method] = Seq.empty // NO NEED
    var newVars: Seq[vpr.LocalVar] = Seq.empty
    // Translation of S_temp := havocSet()
    val havocSTmp = havocSetMethodCall(STmp)
    // Translation of S := S_temp
    val updateProgStates = vpr.LocalVarAssign(currStates, STmp)()

    val forAllTriggers = Seq(vpr.Trigger(Seq(SetState.getInSetApp(Seq(state, STmp))))())
    val existsTriggers = Seq(vpr.Trigger(Seq(SetState.getInSetApp(Seq(state, currStates), useForAll=false, useLimited=true)))())

    // Create safety checks for lookup expressions
    // TODO: Replace all s
    stmt.lookUpAccesses.foreach { luExp =>
      if (luExp.id.typ.isInstanceOf[MapType])
        newStmts = newStmts ++ translateStmt(generateMapAccessCheck(luExp), currStates, currFailureStates, isAutoSelected)._1
      else if (luExp.id.typ.isInstanceOf[SeqType])
        newStmts = newStmts ++ translateStmt(generateSeqAccessCheck(luExp), currStates, currFailureStates, isAutoSelected)._1
      else
        throw UnknownException("Unkown type for lookup discovered")
    }

    stmt match {
      case CompositeStmt(stmts) =>
        // Translate each statement in the sequence
        var resStmts: Seq[vpr.Stmt] = Seq.empty
        var resNewVars: Seq[vpr.LocalVar] = Seq.empty
        var tmpRes = (resStmts, resNewVars)
        for (s <- stmts) {
          tmpRes = translateStmt(s, currStates, currFailureStates)
          resStmts = resStmts ++ tmpRes._1
          resNewVars = resNewVars ++ tmpRes._2
        }
        (resStmts ++ newStmts, resNewVars)

      case PVarDecl(_, _) =>
        // No translation needed here
        // The translation of variable declarations always happens when translating a viper method
        // Either in translateMethod or translateInvariantVerification
        (newStmts, Seq.empty)

      case ProofVarDecl(pv, p) =>
        useAliasForProofVar = true
        currProofVarName = pv.name
        val assertVarExists = vpr.Assert(vpr.Exists(Seq(getAliasForProofVar(pv)), Seq.empty, translateExp(p, state, currStates, currFailureStates))())(info = new Logger(VerificationErrors.Deprecated(p), Logger.ERR)
          .addTitle("Verification Error")
          .addOffset((stmt.offsetLeft, stmt.offsetRight))
          .toAnnotationInfo())
        useAliasForProofVar = false
        val assumeP = vpr.Inhale(translateExp(p, state, currStates, currFailureStates))()
        newStmts = newStmts ++ Seq(assertVarExists, assumeP)
        (newStmts, Seq.empty)

      case AssumeStmt(e) =>

        if (verifierOption != 1) {
          // ForAll
          // Assume forall s: State :: in_set(s, S_tmp) ==> in_set(s, S) && exp
          val exp = vpr.And(SetState.getInSetApp(Seq(state, currStates)),
            translateExp(e, state, currStates, currFailureStates))()
          forallNewStmts = newStmts ++Seq(translateAssumeWithViperExpr(state, STmp, exp, triggers=forAllTriggers))
        }

        if (verifierOption != 0) {
          // Exists
          // Assume forall s: State :: in_set(s, S) && expLeft ==> in_set(s, S_tmp)
          val expRight = SetState.getInSetApp(Seq(state, STmp), useForAll=false)
          val expLeft = translateExp(e, state, currStates, currFailureStates)
          existsNewStmts = newStmts ++Seq(translateAssumeWithViperExpr(state, currStates, expRight, expLeft, useForAll=false, triggers=existsTriggers))
        }

        newStmts = newStmts ++ Seq(havocSTmp) ++ forallNewStmts ++ existsNewStmts ++ Seq(updateProgStates)
        (newStmts, Seq.empty)

      case AssertStmt(e) =>
        val tempFailedStates = vpr.LocalVarDecl(tempFailedStatesVarName, currFailureStates.typ)()
        val havocSFailTmp = havocSetMethodCall(tempFailedStates.localVar)
        val updateSFail = vpr.LocalVarAssign(currFailureStates,
          SetState.getSetUnionApp(Seq(currFailureStates, tempFailedStates.localVar)))()

        if (verifierOption != 1) {
          // ForAll
          val exp1 = vpr.And(SetState.getInSetApp(Seq(state, currStates)),
            translateExp(e, state, currStates, currFailureStates))()
          val exp2 = vpr.And(SetState.getInSetApp(Seq(state, currStates)),
            translateExp(UnaryExpr("!", e), state, currStates, currFailureStates))()
          val stmt1 = translateAssumeWithViperExpr(state, STmp, exp1, triggers=forAllTriggers)
          val forAllFailTriggers = Seq(vpr.Trigger(Seq(SetState.getInSetApp(Seq(state, tempFailedStates.localVar))))())
          val stmt2 = translateAssumeWithViperExpr(state, tempFailedStates.localVar, exp2, triggers=forAllFailTriggers)
          forallNewStmts = Seq(stmt1, stmt2)
        }
        if (verifierOption != 0) {
          // Exists
          val exp1Right = SetState.getInSetApp(Seq(state, STmp), false)
          val exp1Left = translateExp(e, state, currStates, currFailureStates)
          val exp2Right = SetState.getInSetApp(Seq(state, tempFailedStates.localVar), false)
          val exp2Left = translateExp(UnaryExpr("!", e), state, currStates, currFailureStates)
          val stmt1 = translateAssumeWithViperExpr(state, currStates, exp1Right, exp1Left, useForAll=false, triggers=existsTriggers)
          val existsFailTriggers = Seq(vpr.Trigger(Seq(SetState.getInSetApp(Seq(state, currFailureStates), useForAll = false, useLimited = true)))())
          val stmt2 = translateAssumeWithViperExpr(state, currStates, exp2Right, exp2Left, useForAll=false, triggers=existsFailTriggers)
          existsNewStmts = Seq(stmt1, stmt2)
        }
        newStmts = newStmts ++ Seq(havocSTmp, havocSFailTmp) ++ forallNewStmts ++ existsNewStmts ++ Seq(updateSFail, updateProgStates)
        (newStmts, Seq.empty)

      case HyperAssumeStmt(e) =>
        newStmts = newStmts ++ newStmts ++ Seq(vpr.Inhale(translateExp(e, null, currStates, currFailureStates))())
        (newStmts, Seq.empty)

      case stmt@HyperAssertStmt(e) =>
        val assert = vpr.Assert(translateExp(e, null, currStates, currFailureStates))(info = new Logger(VerificationErrors.HyperAssertion(e), Logger.ERR)
          .addTitle("Verification Error")
          .addOffset((stmt.offsetLeft, stmt.offsetRight))
          .toAnnotationInfo())
        newStmts = newStmts ++ Seq(assert)
        (newStmts, Seq.empty)

      case AssignStmt(left, right) =>
        val leftVar = vpr.LocalVarDecl(left.name, vpr.Int)()

        val s0 = vpr.LocalVar(s0VarName, state.typ)()
        val s1 = vpr.LocalVar(s1VarName, state.typ)()

        if (verifierOption != 1) {
          // ForAll
          val exp = vpr.EqCmp(translateExp(left, state, currStates, currFailureStates), translateExp(right, s0, STmp, currFailureStates))()
          val stmt = translateHavocVarHelper(STmp, currStates, state, s0, leftVar, exp, triggers=forAllTriggers)
          forallNewStmts = Seq(stmt)
        }

        if (verifierOption != 0) {
          // Exists
          val exp = vpr.EqCmp(translateExp(left, s1, STmp, currFailureStates), translateExp(right, state, currStates, currFailureStates))()
          val stmt = translateHavocVarHelper(currStates, STmp, state, s1, leftVar, exp, useForAll=false, triggers=existsTriggers)
          existsNewStmts = Seq(stmt)
        }

        newStmts = newStmts ++ Seq(havocSTmp) ++ forallNewStmts ++ existsNewStmts ++ Seq(updateProgStates)
        (newStmts, Seq.empty)

      case MultiAssignStmt(left, right) =>
        val callee = right.method
        if (callee.pre.nonEmpty) {
          useParamsToArgsMap = true
          currParamsToArgsMap = right.paramsToArgs

          callee.pre.foreach{ exp =>
            val vprExp = translateExp(exp, state, currStates, currFailureStates)
            newStmts =  newStmts :+ vpr.Assert(vprExp)(info = new Logger(VerificationErrors.MethodCall(exp), Logger.ERR)
              .addTitle("Verification Error")
              .addOffset((exp.offsetLeft, exp.offsetRight))
              .toAnnotationInfo())
          }

          useParamsToArgsMap = false
        }

        // Havoc S_tmp and S_fail_tmp
        val tempFailedStates = vpr.LocalVar(tempFailedStatesVarName, currFailureStates.typ)()
        val havocSFailTmp = havocSetMethodCall(tempFailedStates)
        val inSetEq = inhaleInSetEqStmt(stateDecl, STmp)
        newStmts = newStmts ++ Seq(havocSTmp, havocSFailTmp) ++ inSetEq

        if (callee.post.nonEmpty) {
          val normalizedPosts = callee.post.map(p => Normalizer.normalize(p, false))
          normalizedPosts.foreach(p => Normalizer.detQuantifier(p, false))
          useParamsToArgsMap = true
          currParamsToArgsMap = right.paramsToArgs
          val translatedPosts = normalizedPosts.map(p => getAssertionWithTriggers(p, STmp, tempFailedStates))
          useParamsToArgsMap = false
          val assumePosts = vpr.Inhale(getAndOfExps(translatedPosts))()
          newStmts = newStmts :+ assumePosts
        }

        // Auto-framing
        if (forAllFrame) {
          val modifiedVars = left.map(v => v.name -> v.typ).toMap
          // For all
          if (verifierOption != 1) {
            val frame = frameUnmodifiedVars(modifiedVars, state, STmp, currStates, true)
            newStmts = newStmts :+ frame
          }
        }

        // Update S and S_fail
        val updateSFail = vpr.LocalVarAssign(currFailureStates,
          SetState.getSetUnionApp(Seq(currFailureStates, tempFailedStates)))()
        newStmts = newStmts ++ Seq(updateSFail, updateProgStates)
        (newStmts, Seq.empty)

      case HavocStmt(id, hintDecl) =>
        val leftVar = State.identifier(id.name)
        val s0 = vpr.LocalVar(s0VarName, state.typ)()
        val s1 = vpr.LocalVar(s1VarName, state.typ)()
        val k = vpr.LocalVarDecl(kVarName, vpr.Int)()

        if (verifierOption != 1) {
          // ForAll
          forallNewStmts = Seq(translateHavocVarHelper(STmp, currStates, state, s0, leftVar, triggers=forAllTriggers))
        }
        if (verifierOption != 0) {
          // Exits
          val inSetTriggerExpr = Seq(SetState.getInSetApp(Seq(state, currStates), useForAll = false, useLimited = true))
          val hintTriggerExpr = if (hintDecl.isEmpty) Seq.empty else Seq(translateHintDecl(hintDecl.get, k.localVar))
          val triggers1 = Seq(vpr.Trigger(inSetTriggerExpr)())
          val triggers2 = Seq(vpr.Trigger(inSetTriggerExpr ++ hintTriggerExpr)())
          val stmt1 = translateHavocVarHelper(currStates, STmp, state, s1, leftVar, triggers=triggers1, useForAll=false)
          val stmt2 = translateHavocVarHelper(currStates, STmp, state, s1, leftVar,
            vpr.EqCmp(
              State.get(s1, id), // TODO: This might break!
              k.localVar)(),
            k, triggers = triggers2, false)
          existsNewStmts = Seq(stmt1, stmt2)
        }
        newStmts = newStmts ++ Seq(havocSTmp) ++ forallNewStmts ++ existsNewStmts ++ Seq(updateProgStates)
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
        val assumeCond = translateStmt(AssumeStmt(cond), ifBlockStates, currFailureStates)

        // Cond not satisfied
        // Let elseBlockStates := S
        val assign2 = vpr.LocalVarAssign(elseBlockStates, currStates)()
        val assumeNotCond = translateStmt(AssumeStmt(UnaryExpr("!", cond)), elseBlockStates, currFailureStates)

        val updateSTmp = vpr.LocalVarAssign(STmp, SetState.getSetUnionApp(Seq(ifBlockStates, elseBlockStates)))()

        val declareBlock = ifStmt.stmts.find(s => s.isInstanceOf[DeclareStmt]).orNull
        val reuseBlock = elseStmt.stmts.find(s => s.isInstanceOf[ReuseStmt]).orNull

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
          val ifRes1 = translateStmt(ifStmt1, ifBlockStates, currFailureStates)
          val elseRes1 = translateStmt(elseStmt1, elseBlockStates, currFailureStates)

          // Use an auxiliary variable to distinguish between ifBlockStates && elseBlockStates
          val isIfBlock = Id(isIfBlockVarName + "_" + alignCounter)
          isIfBlock.typ = IntType()
          val isIfBlockVpr = vpr.LocalVar(isIfBlock.name, vpr.Int)()
          var setFlagForIf: Seq[vpr.Stmt] = Seq.empty
          var setFlagForElse: Seq[vpr.Stmt] = Seq.empty
          if (verifierOption != 1) {
            setFlagForIf = setFlagForIf ++ translateStmt(AssumeStmt(BinaryExpr(isIfBlock, "==", Num(1))), ifBlockStates, currFailureStates)._1
            setFlagForElse = setFlagForElse ++ translateStmt(AssumeStmt(BinaryExpr(isIfBlock, "==", Num(0))), elseBlockStates, currFailureStates)._1
          }
          if (verifierOption != 0) {
            setFlagForIf = setFlagForIf :+ vpr.Inhale(vpr.Forall(Seq(stateDecl), Seq.empty,
              vpr.Implies(SetState.getInSetApp(Seq(state, ifBlockStates), useForAll = false),
                vpr.EqCmp(State.get(state, isIfBlock), one)()
              )())())()
            setFlagForElse = setFlagForElse :+ vpr.Inhale(vpr.Forall(Seq(stateDecl), Seq.empty,
              vpr.Implies(SetState.getInSetApp(Seq(state, elseBlockStates), useForAll = false),
                vpr.EqCmp(State.get(state, isIfBlock), zero)()
              )())())()
          }

          // Get a union of the two sets of states
          val defineAlignedStates = vpr.LocalVarAssign(currStates, SetState.getSetUnionApp(Seq(ifBlockStates, elseBlockStates)))()

          // Verify the aligned statements
          val alignedStmt = translateStmt(declareBlock, currStates, currFailureStates)

          // Separate the two sets of states from the union
          // Forall:
          // S_temp := havoc_set()
          // inhale forall _s: State :: in_set(_s, S_temp) ==> in_set(_s, S) && get(_s, isIfBlock) == 1
          // S1 := S_temp
          // Exists:
          // S_temp := havoc_set()
          // inhale forall _s: State :: in_set(_s, S) && get(_s, isIfBlock) == 1 ==>  in_set(_s, S_temp)
          // S1 := S_temp
          var resumeIfBlockStates: Seq[vpr.Stmt] = Seq(havocSTmp)
          var resumeElseBlockStates: Seq[vpr.Stmt] = Seq(havocSTmp)
          if (verifierOption != 1) {
            resumeIfBlockStates = resumeIfBlockStates :+
              vpr.Inhale(
                vpr.Forall(Seq(stateDecl), Seq.empty,
                  vpr.Implies(SetState.getInSetApp(Seq(state, STmp)),
                    vpr.And(SetState.getInSetApp(Seq(state, currStates)),
                      vpr.EqCmp(State.get(state, isIfBlock),
                        one)())())())()
              )()
            resumeElseBlockStates = resumeElseBlockStates :+
              vpr.Inhale(
                vpr.Forall(Seq(stateDecl), Seq.empty,
                  vpr.Implies(SetState.getInSetApp(Seq(state, STmp), false),
                    vpr.And(SetState.getInSetApp(Seq(state, currStates), false),
                      vpr.EqCmp(State.get(state, isIfBlock),
                        zero)())())())()
              )()
          }
          if (verifierOption != 0) {
            resumeIfBlockStates = resumeIfBlockStates :+ translateStmt(AssumeStmt(BinaryExpr(isIfBlock, "==", Num(1))), currStates, currFailureStates)._1(1)
            resumeElseBlockStates = resumeElseBlockStates :+ translateStmt(AssumeStmt(BinaryExpr(isIfBlock, "==", Num(0))), currStates, currFailureStates)._1(1)
          }

          resumeIfBlockStates = resumeIfBlockStates :+ vpr.LocalVarAssign(ifBlockStates, STmp)()
          resumeElseBlockStates = resumeElseBlockStates :+ vpr.LocalVarAssign(elseBlockStates, STmp)()

          // Verify the rest of the statements in if/else block separately
          val ifRes2 = translateStmt(ifStmt2, ifBlockStates, currFailureStates)
          val elseRes2 = translateStmt(elseStmt2, elseBlockStates, currFailureStates)

          newStmts = newStmts ++ Seq(assign1, assign2) ++ assumeCond._1 ++ assumeNotCond._1 ++ ifRes1._1 ++ elseRes1._1 ++ setFlagForIf ++ setFlagForElse ++ Seq(defineAlignedStates) ++ alignedStmt._1 ++ resumeIfBlockStates ++ resumeElseBlockStates ++ ifRes2._1 ++ elseRes2._1 ++ Seq(updateSTmp, updateProgStates)
          (newStmts, Seq(ifBlockStates, elseBlockStates, isIfBlockVpr) ++ ifRes1._2 ++ elseRes1._2 ++ alignedStmt._2 ++ ifRes2._2 ++ elseRes2._2)
        } else {
          // No alignment
          val ifBlock = translateStmt(ifStmt, ifBlockStates, currFailureStates)
          val elseBlock = translateStmt(elseStmt, elseBlockStates, currFailureStates)
          newStmts = newStmts ++ Seq(assign1) ++ assumeCond._1 ++ ifBlock._1 ++ Seq(assign2) ++ assumeNotCond._1 ++ elseBlock._1 ++ Seq(updateSTmp, updateProgStates)
          (newStmts, Seq(ifBlockStates, elseBlockStates) ++ ifBlock._2 ++ elseBlock._2)
        }
      case DeclareStmt(_, block) =>
        val res = translateStmt(block, currStates, currFailureStates)
        (res._1, res._2)
      case ReuseStmt(_) =>
        throw UnknownException("Reuse statement shouldn't be translated on its own")
      case loop@WhileLoopStmt(cond, body, invWithHints, decr, rule) =>
        // Hints are not actually used
        loopCounter = loopCounter + 1
        val getSkFuncName = "__get_Sk_" + loopCounter
        // Connect all invariants with && to form 1 invariant
        currLoopIndex = zero
        val invs = invWithHints.map(i => i._2) // TODO: Reuse this syntax above

        // append new invariants to the tracker
        invs.foreach(i => {
          if (i.debugId.isEmpty) {
            val id = InvariantTracking.insert(new InvariantDebugInfo(i))
            i.debugId = Some(id)
          }
        })

        // Let currStates == S0 before the loop
        // TODO: redefine this!
        // val S0 = vpr.FuncApp(getSkFuncName, Seq(zero))(vpr.NoPosition, vpr.NoInfo, getConcreteSetStateType(typVarMap), vpr.NoTrafos)
        // val defineS0 = if (verifierOption == 1) Seq(vpr.Inhale(vpr.EqCmp(currStates, S0)())()) else Seq.empty

        //  Assume that S_fail_loop is empty before asserting I(0)
        val loopFailureStatesName = failedStatesVarName + loopCounter
        val loopFailureStates = vpr.LocalVar(loopFailureStatesName, currFailureStates.typ)()
        val assumeEmptyFailureStates = vpr.Inhale(vpr.Forall(
          Seq(stateDecl), Seq.empty, vpr.And(
            vpr.Not(SetState.getInSetApp(Seq(state, loopFailureStates)))(),
            vpr.Not(SetState.getInSetApp(Seq(state, loopFailureStates), useForAll=false))()
          )(),
        )()
        )()

        newVars = Seq(loopFailureStates)

        val normalizedInvariants = if (isAutoSelected) invs else invs.map(i => Normalizer.normalize(i, negate = false))
        if (!isAutoSelected) normalizedInvariants.foreach(i => Normalizer.detQuantifier(i, underForAll = false))

        if (autoSelectRules && rule == "unspecified") {
          // finding correct loop rule
          val normalizedInvWithHints = normalizedInvariants.map(i => (Option.empty, i))

          if (!inline) {
            // Check whether sync(Tot) rule can be applied with a separate Viper program
            val canUseSyncRule = checkSyncCondModular(normalizedInvariants, body, cond) // TODO: Maybe update here
            new Logger("Can use sync rule? " + canUseSyncRule).log()
            if (canUseSyncRule) {
              val useSyncRule = if (loop.isTotal) {
                new Logger("Applying syncTotRule").log()
                val dupLoop = WhileLoopStmt(loop.cond, loop.body, normalizedInvWithHints, decr, "syncTotRule")
                dupLoop.isTotal = true
                translateStmt(dupLoop, currStates, currFailureStates, true)
              } else {
                new Logger("Applying syncRule").log()
                val dupLoop = WhileLoopStmt(loop.cond, loop.body, normalizedInvWithHints, decr, "syncRule")
                dupLoop.isTotal = false
                translateStmt(dupLoop, currStates, currFailureStates, true)
              }
              newStmts = newStmts ++ useSyncRule._1
              newVars = newVars ++ useSyncRule._2
            } else {
              // Sync(Tot) rule cannot be applied, then check if the invariants have a top-level existential quantifier over states
              val invHasTopExists = normalizedInvWithHints.map(i => checkHasTopExists(i._2)).contains(true)
              val useNotSyncRule = if (invHasTopExists) {
                // exists rule
                new Logger("Applying existsRule").log()
                val dupLoop = WhileLoopStmt(loop.cond, loop.body, normalizedInvWithHints, decr, "existsRule")
                dupLoop.isTotal = loop.isTotal
                translateStmt(dupLoop, currStates, currFailureStates, true)
              } else {
                // forall-exists rule
                new Logger("Applying forAllExistsRule").log()
                val dupLoop = WhileLoopStmt(loop.cond, loop.body, normalizedInvWithHints, decr, "forAllExistsRule")
                dupLoop.isTotal = loop.isTotal
                translateStmt(dupLoop, currStates, currFailureStates, true)
              }
              newStmts = newStmts ++ useNotSyncRule._1
              newVars = newVars ++ useNotSyncRule._2
            }
          } else {
            val loopStates = vpr.LocalVar("S_loop" + loopCounter, currStates.typ)()
            val havocCurrStates = havocSetMethodCall(loopStates)
            val havocFailureStates = havocSetMethodCall(loopFailureStates)

            val inSetEq = inhaleInSetEqStmt(stateDecl, loopStates)
            val inSetEqFail = inhaleInSetEqStmt(stateDecl, loopFailureStates)
            val inhaleI = vpr.Inhale(getAllInvariantsWithTriggers(normalizedInvariants, loopStates, loopFailureStates))()

            val checkRuleCond = vpr.LocalVar(checkSyncCondName + loopCounter, vpr.Bool)()
            val s1 = State.localVarDecl(s1VarName)
            val s2 = State.localVarDecl(s2VarName)
            val sameGuardValue = vpr.Forall(Seq(s1, s2), Seq.empty, vpr.Implies(
              vpr.And(SetState.getInSetApp(Seq(s1.localVar, loopStates)), SetState.getInSetApp(Seq(s2.localVar, loopStates)))(),
              vpr.EqCmp(translateExp(cond, s1.localVar, loopStates, loopFailureStates), translateExp(cond, s2.localVar, loopStates, loopFailureStates))()
            )())()
            val assignToCondVar = vpr.LocalVarAssign(checkRuleCond, sameGuardValue)()

            newStmts = newStmts ++ Seq(havocCurrStates, havocFailureStates) ++ inSetEq ++ inSetEqFail ++ Seq(inhaleI, assignToCondVar)
            newVars = newVars ++ Seq(loopStates, checkRuleCond)

            // If branch
            val useSyncRule = if (loop.isTotal) {
              val dupLoop = WhileLoopStmt(loop.cond, loop.body, normalizedInvWithHints, decr, "syncTotRule")
              dupLoop.isTotal = true
              translateStmt(dupLoop, currStates, currFailureStates, true)
            } else {
              val dupLoop = WhileLoopStmt(loop.cond, loop.body, normalizedInvWithHints, decr, "syncRule")
              dupLoop.isTotal = false
              translateStmt(dupLoop, currStates, currFailureStates, true)
            }

            // Else branch
            val invHasTopExists = normalizedInvWithHints.exists(i => i._2.isInstanceOf[Assertion] && i._2.asInstanceOf[Assertion].topExists)
            val useNotSyncRule = if (invHasTopExists) {
              // exists rule
              val dupLoop = WhileLoopStmt(loop.cond, loop.body, normalizedInvWithHints, decr, "existsRule")
              dupLoop.isTotal = loop.isTotal
              translateStmt(dupLoop, currStates, currFailureStates, true)
            } else {
              // forall-exists rule
              val dupLoop = WhileLoopStmt(loop.cond, loop.body, normalizedInvWithHints, decr, "forAllExistsRule")
              dupLoop.isTotal = loop.isTotal
              translateStmt(dupLoop, currStates, currFailureStates, true)
            }
            val applyRule = vpr.If(checkRuleCond, vpr.Seqn(useSyncRule._1, Seq.empty)(), vpr.Seqn(useNotSyncRule._1, Seq.empty)())()

            newStmts = newStmts :+ applyRule
            newVars = newVars ++ useSyncRule._2 ++ useNotSyncRule._2
          }
        } else {
          // A rule has been determined, either automatically or by the user
          if (!isAutoSelected && !syncTotWarningPrinted && postIsTopExists && rule != "syncTotRule" && rule != "existsRule") {
            new Logger("Warning: method " + currMethod.mName + " has a postcondition " +
              "which has a top-level existential quantifier over states, \n " +
              "        but syncTotRule or existsRule is not chosen for at least one of the loops in the method. \n " +
              "        Please make sure that every non-nested loop uses syncTotRule. \n" +
              "         Ignore this warning if you have already done so. ", Logger.WARN)
            syncTotWarningPrinted = true
          }

          if (rule=="forAllExistsRule") {
            normalizedInvariants.foreach(i => {
              val canUseForAllExistsRule = checkForAllExistsRuleSideCondition(i, false)
              if (!canUseForAllExistsRule) {
                if (!isAutoSelected) throw UnknownException("When using forAllExistsRule, the invariant must satisfy the condition " +
                  "that there are no forall quantifiers over states after an exists quantifier. ")
                else {
                  throw UnknownException("The forAllExistsRule automatically selected cannot be applied, because at least one of the invariants does not satisfy the condition " +
                    "that there are no forall quantifiers over states after an exists quantifier. Please revise the loop invariants. ")
                }
              }
            })
          }

          if (!isAutoSelected && rule == "existsRule") {
            val invHasTopExists = normalizedInvariants.exists(i => checkHasTopExists(i))
            if (!invHasTopExists) throw UnknownException("To use the existsRule, at least one of the invariants must contain a top-level " +
              "existential quantifier that quantifies over states")
          }

          newStmts = newStmts ++ Seq(assumeEmptyFailureStates)

          // Assert I(0)
          if (normalizedInvariants.nonEmpty) {
            for ((normalizedInv, i) <- normalizedInvariants.zipWithIndex) {
              val oInv = InvariantTracking.get(normalizedInv.debugId.get).inv
              val qc = InvariantTracking.get(normalizedInv.debugId.get).quantifiersRemoved

              newStmts = newStmts :+ vpr.Assert(translateExp(normalizedInv, null, currStates, loopFailureStates))(info = new Logger(VerificationErrors.LoopEntryPoint(oInv), Logger.ERR)
                .addTitle("Verification Error")
                .addQuantifiersRemoved(qc)
                .addWhileRule(rule)
                .addOffset((invs(i).offsetLeft, invs(i).offsetRight))
                .toAnnotationInfo())
            }
          }

          // Use the rule specified by the user
          if (rule == "existsRule") {
            // Generating new methods
            val newMethod1 = translateExistsRuleCond1(normalizedInvariants, cond, body, decr.get)
            val newMethod2 = translateExistsRuleCond2(normalizedInvariants, cond, body, decr.get)
            // Appending new methods
            val newMethods = Seq(newMethod1, newMethod2)
            allMethods = allMethods ++ newMethods
          } else  {
            if (inline) {
              val invVerification = translateInvariantVerificationInline(normalizedInvariants, cond, body, decr, currStates, loopFailureStates, rule, isAutoSelected)
              newStmts = newStmts ++ invVerification._1
              newVars = newVars ++ invVerification._2
            } else {
              val newMethod = translateInvariantVerificationModular(invs, normalizedInvariants, cond, body, decr, rule, isAutoSelected)
              allMethods = allMethods ++ newMethod
            }
          }

          val havocFailureStates = havocSetMethodCall(loopFailureStates)
          newStmts = newStmts ++ Seq(havocSTmp, havocFailureStates)

          // Auto-framing
          if (forAllFrame) {
            if (verifierOption != 1) newStmts = newStmts :+ frameUnmodifiedVars(body.modifiedProgVars, state, STmp, currStates, true)
            if (verifierOption != 0 && loop.isTotal && existsFrame) newStmts = newStmts :+ frameUnmodifiedVars(body.modifiedProgVars, state, currStates, STmp, false)
            newStmts = newStmts ++ inhaleInSetEqStmt(stateDecl, STmp)
          }

          // Update S after the loop
          if (rule == "syncRule") {
            val translatedInv = getAllInvariantsWithTriggers(normalizedInvariants, STmp, loopFailureStates)
            val empS = vpr.Forall(Seq(stateDecl), Seq.empty, vpr.Not(SetState.getInSetApp(Seq(state, STmp), false))())()
            newStmts = newStmts :+ vpr.Inhale(vpr.Or(translatedInv, empS)())()
          } else if (rule == "forAllExistsRule") {
            val transformedInvs = normalizedInvariants.map(i => transformExpr(i, cond, false))
            val translatedInv = getAllInvariantsWithTriggers(transformedInvs, STmp, loopFailureStates)
            newStmts = newStmts :+ vpr.Inhale(translatedInv)()
          } else if (rule == "syncTotRule" || rule == "existsRule") {
            val translatedInv = getAllInvariantsWithTriggers(normalizedInvariants, STmp, loopFailureStates)
            newStmts = newStmts :+ vpr.Inhale(translatedInv)()
          }

          // S_fail = S_fail union S_loop_fail
          val updateSFail = vpr.LocalVarAssign(currFailureStates, SetState.getSetUnionApp(Seq(currFailureStates, loopFailureStates)))()
          newStmts = newStmts ++ Seq(updateSFail, updateProgStates)
          if (rule == "desugaredRule" || rule == "forAllExistsRule") {
            val notCond = translateStmt(AssumeStmt(UnaryExpr("!", cond)), currStates, currFailureStates)
            newStmts = newStmts ++ notCond._1
          } else {
            // Inhale not b
            val negatedLoopGuard = translateExp(UnaryExpr("!", cond), state, currStates, currFailureStates)
            val notCondForAll = translateAssumeWithViperExpr(state, currStates, negatedLoopGuard, triggers=forAllTriggers)
            // val notCondExists = translateAssumeWithViperExpr(state, currStates, negatedLoopGuard, typVarMap, useForAll=false)
            newStmts = newStmts :+ notCondForAll
          }
        }

        (newStmts, newVars)

      case FrameStmt(exp, body) =>
        val framedExpr = translateExp(exp, state, currStates, currFailureStates)
        val assertFrame = vpr.Assert(framedExpr)(info = new Logger(VerificationErrors.HyperAssertion(exp), Logger.ERR)
          .addTitle("Verification Error")
          .addOffset((exp.offsetLeft, exp.offsetRight))
          .toAnnotationInfo())
        val translatedBody = translateStmt(body, currStates, currFailureStates)
        val inhaleFrame = vpr.Inhale(framedExpr)()
        (Seq(assertFrame) ++ translatedBody._1 ++ Seq(inhaleFrame), translatedBody._2)

      case UseHintStmt(hint) =>
        newStmts = newStmts ++ Seq(vpr.Inhale(translateExp(hint, state, currStates, currFailureStates))())
        (newStmts, Seq.empty)

      case call@MethodCallStmt(_, _) =>
        // Assert the callee's precondition
        if (call.method.pre.nonEmpty) {
          useParamsToArgsMap = true
          currParamsToArgsMap = call.paramsToArgs
          call.method.pre.foreach{ precondition =>
            newStmts :+ vpr.Assert(translateExp(precondition, state, currStates, currFailureStates))(info = new Logger(VerificationErrors.MethodCall(precondition), Logger.ERR)
              .addTitle("Verification Error")
              .addOffset((precondition.offsetLeft, stmt.offsetRight))
              .toAnnotationInfo())
          }
          useParamsToArgsMap = false
        }

        // Havoc S_tmp and S_fail_tmp
        val tempFailedStates = vpr.LocalVar(tempFailedStatesVarName, currFailureStates.typ)()
        val havocSFailTmp = havocSetMethodCall(tempFailedStates)
        val inSetEq = inhaleInSetEqStmt(stateDecl, STmp)
        newStmts = newStmts ++ Seq(havocSTmp, havocSFailTmp) ++ inSetEq

        // Assume the callee's postcondition
        if (!call.method.post.isEmpty) {
          useParamsToArgsMap = true
          currParamsToArgsMap = call.paramsToArgs
          val normalizedPosts = call.method.post.map(p => Normalizer.normalize(p, false))
          normalizedPosts.foreach(p => Normalizer.detQuantifier(p, false))
          val translatedPosts = normalizedPosts.map(p => getAssertionWithTriggers(p, STmp, tempFailedStates))
          useParamsToArgsMap = false
          val assumePosts = vpr.Inhale(getAndOfExps(translatedPosts))()
          newStmts = newStmts :+ assumePosts
        }

        // Auto-framing
        if (forAllFrame)  {
          // For all
          if (verifierOption != 1) {
            val frame = frameUnmodifiedVars(Map.empty, state, STmp, currStates, true)
            newStmts = newStmts :+ frame
          }
        }

        // Update S and S_fail
        val updateSFail = vpr.LocalVarAssign(currFailureStates,
          SetState.getSetUnionApp(Seq(currFailureStates, tempFailedStates)))()
        newStmts = newStmts ++ Seq(updateSFail, updateProgStates)
        (newStmts, Seq.empty)
    }
  }

  def transformExpr(e: Expr, loopGuard: Expr, transform: Boolean): Expr = {
    e match {
      case a@Assertion(quantifier, assertVarDecls, body) =>
        val newAssertion = if (quantifier == "forall") {
          Assertion(quantifier, assertVarDecls, transformExpr(body, loopGuard, transform))
        } else {
          // Note that all assertion variables either have type State or primitive types
          val transformBody = assertVarDecls(0).vType.isInstanceOf[StateType]
          Assertion(quantifier, assertVarDecls, transformExpr(body, loopGuard, transformBody))
        }
        newAssertion.typ = a.typ
        newAssertion.topExists = a.topExists
        newAssertion.proForAll = a.proForAll
        newAssertion.triggers = a.triggers
        newAssertion
      case BinaryExpr(e1, op, e2) => BinaryExpr(transformExpr(e1, loopGuard, transform), op, transformExpr(e2, loopGuard, transform))
      case UnaryExpr(op, e) => UnaryExpr(op, transformExpr(e, loopGuard, transform))
      case StateExistsExpr(state, _) =>
        if (transform) BinaryExpr(getExprInState(loopGuard, state), "||", e)
        else e
      case _ => e
    }
  }

  // Manual access check before looking up objects in Maps
  def generateMapAccessCheck(luExp: LookupExpr): Stmt = AssertStmt(
    CombExpr(
      luExp.index,
      luExp.id,
      "in"
    )
  )

  // Manual access check before looking up objects in Sequences
  def generateSeqAccessCheck(luExp: LookupExpr): Stmt = AssertStmt(
    BinaryExpr(
      BinaryExpr(
        Num(0),
        "<=",
        luExp.index
      ),
      "&&",
      BinaryExpr(
        luExp.index,
        "<",
        LengthExpr(luExp.id)
      )
    )
  )

  def getExprInState(e: Expr, state: SpecialId): Expr = {
    e match {
      case id@Id(_) => LookupExpr(state, id)
      case ImpliesExpr(left, right) => ImpliesExpr(getExprInState(left, state), getExprInState(right, state))
      case BinaryExpr(e1, op, e2) => BinaryExpr(getExprInState(e1, state), op, getExprInState(e2, state))
      case UnaryExpr(op, body) => UnaryExpr(op, getExprInState(body, state))
      case _ => e
    }
  }

  // This returns:
  // forall s: State :: in_set(s, S1) ==>
  //    exists s': State :: in_set(s', S2) &&
  //      (forall progVar: Int :: progVar != modVar ==> get(s', progVar) == get(state, progVar))
  def frameUnmodifiedVars(modifiedVars: Map[String, Type], state: vpr.LocalVar, S1: vpr.LocalVar, S2: vpr.LocalVar, useForAll: Boolean): vpr.Stmt = {
    val s_prime = vpr.LocalVarDecl(if (useForAll) s0VarName else s1VarName, state.typ)()
    val vVar = vpr.LocalVarDecl(progVarName, vpr.Int)()
    val vVarId = Id(progVarName)
    vVarId.typ = IntType()

    val rightExpr = if (modifiedVars.isEmpty) {
      vpr.Exists(Seq(s_prime), Seq.empty,
        vpr.And(SetState.getInSetApp(Seq(s_prime.localVar, S2), useForAll),
          vpr.Forall(Seq(vVar), Seq.empty,
            vpr.EqCmp(State.get(s_prime.localVar, vVarId),
              State.get(state, vVarId))()
          )()
        )()
      )()
    } else {

      // modifiedVarsVpr is guaranteed to be non-empty
      val modifiedVarsVpr = modifiedVars.map(v => vpr.LocalVar(v._1, v._2 match {
        case _: StateType => translateType(v._2)
        case _: StmtBlockType => translateType(v._2)
        case _: UnknownType => translateType(v._2)
        case _ => vpr.Int
      })()) // TODO: Fix this like before

      vpr.Exists(Seq(s_prime), Seq.empty,
        vpr.And(SetState.getInSetApp(Seq(s_prime.localVar, S2), useForAll),
          vpr.Forall(Seq(vVar), Seq.empty,
            vpr.Implies(
              getAndOfExps(
                modifiedVarsVpr.map(t => vpr.NeCmp(vVar.localVar, t)()).toList
              ),
              getAndOfExps(
                TypeChecker.declaredTypes.map(typ => {
                  vVarId.typ = typ
                  vpr.EqCmp(
                    State.get(s_prime.localVar, vVarId),
                    State.get(state, vVarId)
                  )()
                }).toList
              )
            )()
          )()
        )()
      )()
    }

    val trigger = vpr.Trigger(Seq(SetState.getInSetApp(Seq(state, S1), useForAll = useForAll, useLimited = (!useForAll))))()
    translateAssumeWithViperExpr(state, S1, rightExpr, triggers = Seq(trigger), useForAll = useForAll)
  }

  def checkSyncCondModular(normalizedInv: Seq[Expr], body: CompositeStmt, loopGuard: Expr): Boolean = {
    // println(f"Invariants: ${normalizedInv}\nloopGuard: $loopGuard")
    val inputStates = SetState.localVarDecl("S0")
    val outputStates = SetState.localVarDecl("SS")
    val inputFailureStates = SetState.localVarDecl("S0_fail")
    val outputFailureStates = SetState.localVarDecl("SS_fail")

    val s1 = State.localVarDecl(s1VarName)
    val s2 = State.localVarDecl(s2VarName)

    // I
    val pre1 = getAllInvariantsWithTriggers(normalizedInv, inputStates.localVar, inputFailureStates.localVar)
    // All program variables are different

    val allProgVarsInLoopBody = body.allProgVars.map(v => vpr.LocalVar(v._1, v._2 match {
      case _: StateType => translateType(v._2)
      case _: StmtBlockType => translateType(v._2)
      case _: UnknownType => translateType(v._2)
      case _ => vpr.Int
    })()).toSeq
    val (allIntVars, stateVars, allOtherVars, pre2) = separateVarsByType(allProgVarsInLoopBody)

    val args = (allIntVars ++ stateVars).map(v => vpr.LocalVarDecl(v.name, v.typ)())

    // post
    val sameGuardValue = vpr.Forall(Seq(s1, s2), Seq.empty, vpr.Implies(
      vpr.And(SetState.getInSetApp(Seq(s1.localVar, outputStates.localVar)), SetState.getInSetApp(Seq(s2.localVar, outputStates.localVar)))(),
      vpr.EqCmp(translateExp(loopGuard, s1.localVar, outputStates.localVar, outputFailureStates.localVar), translateExp(loopGuard, s2.localVar, outputStates.localVar, outputFailureStates.localVar))()
    )())(info = new Logger(VerificationErrors.LoopSyncGuard(loopGuard), Logger.ERR)
      .addTitle("Verification Error")
      .addOffset((loopGuard.offsetLeft,
      loopGuard.offsetRight))
      .toAnnotationInfo())

    val method = createViperMethod(checkSyncCondMethodName, // no update needed
      args, // Args
      Seq.empty,
      Seq(pre1) ++ pre2,  // Pres
      Seq(sameGuardValue),  // Posts
      Seq.empty, Seq.empty)

    val preamble = generatePreamble()
    val program = vpr.Program(preamble._1, Seq.empty, Seq.empty, Seq.empty, preamble._2 ++ Seq(method), Seq.empty)()
    val res = ViperRunner.runSiliconAndCarbon(program, 5, 10, true)
    ViperRunner.interpretResult(res)
  }

  // Returns true if e satisfies the condition that there are no forall quantifiers over states after an exists quantifier
  // Note that the input e is expected to be normalized, so e contains no implications
  def checkForAllExistsRuleSideCondition(e: Expr, underExists: Boolean): Boolean = {
    e match {
      case Assertion(quantifier, vars, body) =>
        if (quantifier == "exists") checkForAllExistsRuleSideCondition(body, true)
        else {
          val quantifiesOverStates = vars.filter(v => v.vName.typ.isInstanceOf[StateType]).size > 0
          if (quantifiesOverStates && underExists) false
          else checkForAllExistsRuleSideCondition(body, underExists)
        }
      case UnaryExpr(_, e) => checkForAllExistsRuleSideCondition(e, underExists)
      case BinaryExpr(e1, _, e2) => checkForAllExistsRuleSideCondition(e1, underExists) && checkForAllExistsRuleSideCondition(e2, underExists)
      case _ => true
    }
  }

  def getAssertionWithTriggers(assertion: Expr, currStates: vpr.Exp, failureStates: vpr.Exp): vpr.Exp = {
    needTriggers = true
    val translatedExpr = translateExp(assertion, null, currStates, failureStates)
    needTriggers = false
    translatedExpr
  }

  def getAllInvariantsWithTriggers(normalizedInvs: Seq[Expr], currStates: vpr.Exp, failureStates: vpr.Exp): vpr.Exp = {
    if (normalizedInvs.isEmpty) return trueLit
    val translatedInvs = normalizedInvs.map(i => getAssertionWithTriggers(i, currStates, failureStates))
    getAndOfExps(translatedInvs)
  }

  def getAllInvariants(invs: Seq[Expr], currStates: vpr.Exp, failureStates: vpr.Exp): vpr.Exp = {
    if (invs.isEmpty) return trueLit
    val translatedInvs = invs.map(i => translateExp(i, null, currStates, failureStates))
    getAndOfExps(translatedInvs)
  }

  /*  This creates a Viper method as shown below:
  *   method methodName(S0: SetState[Int], S0_fail: SetState[Int], ...) returns (SS: SetState[Int], SS_fail: SetState[Int], ...)
  *   requires methodPres
  *   ensures methodPosts
  *   {
  *       methodLocalVars
  *       in_set_forall == in_set_exists and in_set_forall_limited == in_set_exists_limited in S0
  *       SS := S0
  *       SS_fail := S0_fail
  *       methodBody
  *   }
  * */
  def createViperMethod(methodName: String, args: Seq[vpr.LocalVarDecl], res: Seq[vpr.LocalVarDecl], methodPres: Seq[vpr.Exp], methodPosts: Seq[vpr.Exp], body: Seq[vpr.Stmt], methodLocalVars: Seq[vpr.LocalVarDecl]) : vpr.Method = { // NO NEED
    val inputStates = SetState.localVarDecl("S0")
    val outputStates = SetState.localVarDecl("SS")
    val inputFailureStates = SetState.localVarDecl("S0_fail")
    val outputFailureStates = SetState.localVarDecl("SS_fail")

    val state = State.localVarDecl(sVarName)

    val methodArgs = Seq(inputStates, inputFailureStates) ++ args
    val methodRes = Seq(outputStates, outputFailureStates) ++ res
    var methodBody: Seq[vpr.Stmt] = Seq.empty

    // The following statement assumes in_set_forall == in_set_exists for all states in S0 and S0_fail
    val inSetEq = inhaleInSetEqStmt(state, inputStates.localVar)
    val inSetEqFail = inhaleInSetEqStmt(state, inputFailureStates.localVar)
    // SS := S0
    val assignToOutputStates = vpr.LocalVarAssign(outputStates.localVar, inputStates.localVar)()
    // SS_fail := S0_fail
    val assignToOutputFailureStates = vpr.LocalVarAssign(outputFailureStates.localVar, inputFailureStates.localVar)()
    methodBody = methodBody ++ inSetEq ++ inSetEqFail ++ Seq(assignToOutputStates, assignToOutputFailureStates)
    methodBody = methodBody ++ body

    vpr.Method(methodName, methodArgs, methodRes, methodPres, methodPosts,
      Option(vpr.Seqn(methodBody, methodLocalVars.map(i => vpr.LocalVarDecl(i.name, i.typ)()))()))()
  }

  def verifyStmtModular(methodName: String, stmt: Stmt, allProgVarsInStmt: Seq[vpr.LocalVar], pres: Seq[Expr], posts: Seq[(Expr, Option[Info])]): vpr.Method = {
    val inputStates = SetState.localVarDecl("S0")
    val outputStates = SetState.localVarDecl("SS")
    val inputFailureStates = SetState.localVarDecl("S0_fail")
    val outputFailureStates = SetState.localVarDecl("SS_fail")

    val tmpStates = SetState.localVar(tempStatesVarName)
    val tmpFailureStates = SetState.localVar(tempFailedStatesVarName)

    var methodLocalVars = Seq(tmpStates, tmpFailureStates)
    var methodPres = pres.map(i => getAssertionWithTriggers(i, inputStates.localVar, inputFailureStates.localVar))
    val methodPosts = posts.map{ case (inv, info) =>
      if (info.nonEmpty) translateExp(inv, null, outputStates.localVar, outputFailureStates.localVar, info = info.get)
      else translateExp(inv, null, outputStates.localVar, outputFailureStates.localVar)
    }

    val translatedStmt = translateStmt(stmt, outputStates.localVar, outputFailureStates.localVar)
    val methodBody = translatedStmt._1
    val auxiliaryVars = translatedStmt._2

    val (allIntProgVars, stateVars, _, _) = separateVarsByType(allProgVarsInStmt)
    val (allIntVars, _, allOtherVars, preVarsDiff) = separateVarsByType(allIntProgVars ++ auxiliaryVars)
    methodLocalVars = methodLocalVars ++ allOtherVars
    val args = (allIntVars ++ stateVars).map(v => vpr.LocalVarDecl(v.name, v.typ)())
    methodPres = methodPres ++ preVarsDiff

    // println(f"allProgVarsInStmt: $allProgVarsInStmt\nallIntProgVars: $allIntProgVars\nstateVars: $stateVars\nallIntVars: $allIntVars\nallOtherVars: $allOtherVars\npreVarsDiff: $preVarsDiff")

    createViperMethod(methodName, args, Seq.empty, methodPres, methodPosts, methodBody, methodLocalVars.map(i => vpr.LocalVarDecl(i.name, i.typ)()))
  }

  // This returns a sequence of int variables and a sequence of non-int variables
  // And an expression that ensures that all int variables are unique
  def separateVarsByType(vars: Seq[vpr.LocalVar]): (Seq[vpr.LocalVar], Seq[vpr.LocalVar], Seq[vpr.LocalVar], Seq[vpr.Exp]) = {
    val allIntVars = vars.filter(v => v.typ == vpr.Int)
    val stateVars = vars.filter(v => v.typ == State.stateType)
    val allOtherVars = vars.diff(allIntVars ++ stateVars)
    val allIntVarsWithValues = allIntVars.map(v => vpr.EqCmp(v, vpr.IntLit(allIntVars.indexOf(v))())())
    val exp: Seq[vpr.Exp] = if (allIntVarsWithValues.isEmpty) Seq.empty else Seq(allIntVarsWithValues.reduce((e1: vpr.Exp, e2: vpr.Exp) => vpr.And(e1, e2)()))

    (allIntVars, stateVars, allOtherVars, exp)
  }

  // e is exptected to be normalized, so it shouldn't contain any implications
  def checkHasTopExists(e: Expr): Boolean = {
    e match {
      case a@Assertion(_, _, _) => a.topExists
      case BinaryExpr(e1, op, e2) =>
        if (TypeChecker.boolOp.contains(op) && op == "&&") checkHasTopExists(e1) || checkHasTopExists(e2)
        else false
      case UnaryExpr(op, e) =>
        if (TypeChecker.boolOp.contains(op)) checkHasTopExists(e)
        else false
      case _ => false
    }
  }

  // e is exptected to be normalized, so it shouldn't contain any implications
  // e is expected to contain a top-level existential quantifier
  def addToTopExists(e: Expr, toAdd: Expr): Expr = {
    e match {
      case a@Assertion(quantifier, assertVarDecls, body) =>
        val newBody = if (a.topExists) {
          val newConjunct = getExprInState(toAdd, assertVarDecls.head.vName)
          BinaryExpr(body, "&&", newConjunct)
        } else addToTopExists(body, toAdd)
        val newAssertion = Assertion(quantifier, assertVarDecls, newBody)
        newAssertion.topExists = a.topExists
        newAssertion.proForAll = a.proForAll
        newAssertion.triggers = a.triggers
        newAssertion
      case BinaryExpr(e1, op, e2) =>
        val newE1 = addToTopExists(e1, toAdd)
        val newE2 = addToTopExists(e2, toAdd)
        BinaryExpr(newE1, op, newE2)
      case UnaryExpr(op, e) =>
        val newExpr = addToTopExists(e, toAdd)
        UnaryExpr(op, newExpr)
      case _ => e
    }
  }

  // e is expected to be normalized and has a top-level existential quantifier
  // Remove the state that is quantified by a top-level existential quantifier
  // For every occurrence of the removed state, replace it with another state whose identifier is "_" + removed state identifier
  def removeTopExistsState(e: Expr, stateToRemove: String=""): Expr = {
    val ret = e match {
      case a@Assertion(quantifier, assertVarDecls, body) =>
        if (a.topExists && stateToRemove == "") {
          val stateToRemove = a.assertVarDecls.head.vName.name
          stateRemoved = stateToRemove
          val newBody = removeTopExistsState(body, stateToRemove)
          val newAssertVarDecls = assertVarDecls.drop(1)
          if (newAssertVarDecls.length == 0) newBody
          else {
            val newAssertion = Assertion(quantifier, newAssertVarDecls, newBody)
            newAssertion.topExists = true
            newAssertion.proForAll = false
            // newAssertion shouldn't have triggers
            newAssertion
          }
        } else {
          val newBody = removeTopExistsState(body, stateToRemove)
          val newAssertion = Assertion(quantifier, assertVarDecls, newBody)
          newAssertion.topExists = a.topExists
          newAssertion.proForAll = a.proForAll
          newAssertion.triggers = a.triggers
          newAssertion
        }
      case BinaryExpr(e1, op, e2) =>
        val newE1 = removeTopExistsState(e1, stateToRemove)
        val newE2 = removeTopExistsState(e2, stateToRemove)
        BinaryExpr(newE1, op, newE2)
      case UnaryExpr(op, e) =>
        val newBody = removeTopExistsState(e, stateToRemove)
        UnaryExpr(op, newBody)
      case ImpliesExpr(left, right) =>
        val newLeft = removeTopExistsState(left, stateToRemove)
        val newRight = removeTopExistsState(right, stateToRemove)
        ImpliesExpr(newLeft, newRight)
        // TODO: THIS MUST BE ADAPTED ABOVE
      /*case GetValExpr(state, id) =>
        if (state.idName != stateToRemove) e
        else {
          val newStateVar = AssertVar(stateAliasPrefix + stateToRemove + "_" + stateVarCounter)
          newStateVar.typ = state.typ
          GetValExpr(newStateVar, id)
        }*/
      case expr@LookupExpr(id, index) =>
        if (id.typ.isInstanceOf[StateType]) {
          if (id.asInstanceOf[SpecialId].idName != stateToRemove) e
          else {
            val newStateVar = AssertVar(stateAliasPrefix + stateToRemove + "_" + stateVarCounter)
            newStateVar.typ = id.typ
            LookupExpr(newStateVar, index)
          }
        } else {
          expr
        }
      case StateExistsExpr(state, _) =>
        if (state.idName != stateToRemove) e
        else BoolLit(true)
      case _ => e
    }
    ret.setOffsets(e.offsetLeft + 7, e.offsetRight)
    ret.debugId = e.debugId
    ret
  }

  def translateExistsRuleCond1(normalizedInvs: Seq[Expr], loopGuard: Expr, body: CompositeStmt, decrExpr: Expr): vpr.Method = {
    val methodName = checkExistsRuleCond1MethodName + "_" + loopCounter
    val tViperVar = vpr.LocalVar(tVarName + loopCounter, vpr.Int)()
    val tProgVar = Id(tViperVar.name)
    tProgVar.typ = IntType()
    val stmt = IfElseStmt(loopGuard, body, CompositeStmt(Seq.empty))
    val varsInStmt = body.allProgVars.map(v => vpr.LocalVar(v._1, v._2 match {
      case _: StateType => translateType(v._2)
      case _: StmtBlockType => translateType(v._2)
      case _: UnknownType => translateType(v._2)
      case _ => vpr.Int
    })()).toSeq ++ Seq(tViperVar)
    var pres: Seq[Expr] = Seq.empty
    var posts: Seq[(Expr, Option[Info])] = Seq.empty

    // Find the first invariant that contains a top-level existential quantifier
    val firstExistsInv = normalizedInvs.find(i => checkHasTopExists(i) == true).get
    pres = normalizedInvs.diff(Seq(firstExistsInv))
    posts = pres.map(inv => {
      val oInv = InvariantTracking.get(inv.debugId.get).inv
      val qc = InvariantTracking.get(inv.debugId.get).quantifiersRemoved

      (
        inv,
        Option(new Logger(VerificationErrors.LoopInvariant(oInv), Logger.ERR)
          .addTitle("Verification Error")
          .addQuantifiersRemoved(qc)
          .addWhileRule("existsRule")
          .addOffset((inv.offsetLeft, inv.offsetRight))
          .toAnnotationInfo())
      )
    })

    val exprAddedToPre = BinaryExpr(loopGuard, "&&", BinaryExpr(tProgVar, "==", decrExpr))
    pres = pres :+ addToTopExists(firstExistsInv, exprAddedToPre)

    val exprAddedToPost = BinaryExpr(BinaryExpr(decrExpr, ">=", Num(0)), "&&", BinaryExpr(decrExpr, "<", tProgVar))
    val temp = (addToTopExists(firstExistsInv, exprAddedToPost), Option(new Logger(VerificationErrors.LoopVariant(decrExpr), Logger.ERR)
      .addTitle("Verification Error 1")
      .addOffset((decrExpr.offsetLeft, decrExpr.offsetRight))
      .toAnnotationInfo()))
    posts = posts :+ temp

    verifyStmtModular(methodName, stmt, varsInStmt, pres, posts)
  }

  def translateExistsRuleCond2(normalizedInvs: Seq[Expr], loopGuard: Expr, body: CompositeStmt, decrExpr: Expr): vpr.Method = {
    val methodName = checkExistsRuleCond2MethodName + "_" +loopCounter
    var varsInStmt = body.allProgVars.map(v => vpr.LocalVar(v._1, v._2 match {
      case _: StateType => translateType(v._2)
      case _: StmtBlockType => translateType(v._2)
      case _: UnknownType => translateType(v._2)
      case _ => vpr.Int
    })()).toSeq
    var pres: Seq[Expr] = Seq.empty
    var posts: Seq[(Expr, Option[Info])] = Seq.empty

    // Find the first invariant that contains a top-level existential quantifier
    val firstExistsInv = normalizedInvs.find(i => checkHasTopExists(i)).get
    pres = normalizedInvs.diff(Seq(firstExistsInv))
    posts = pres.map(inv => (inv, Option(null)))

    val newInv = removeTopExistsState(firstExistsInv, "")
    // update removed quantifier count
    InvariantTracking.get(firstExistsInv.debugId.get).incrRemovedQuantifier()
    val oInv = InvariantTracking.get(firstExistsInv.debugId.get).inv
    val qc = InvariantTracking.get(firstExistsInv.debugId.get).quantifiersRemoved

    val newState = State.localVar(stateAliasPrefix + stateRemoved + "_" + stateVarCounter)
    stateVarCounter = stateVarCounter + 1
    varsInStmt = varsInStmt :+ newState
    body.allProgVars +=  (newState.name -> StateType())
    pres = pres :+ newInv
    val temp = (
      newInv,
      Option(new Logger(VerificationErrors.LoopInvariant(oInv), Logger.ERR)
        .addTitle("Verification Error")
        .addQuantifiersRemoved(qc)
        .addWhileRule("existsRule")
        .addOffset((oInv.offsetLeft, oInv.offsetRight))
        .toAnnotationInfo())
    )
    posts = posts :+ temp

    val stmt = WhileLoopStmt(loopGuard, body, pres.map(i => (Option.empty, i)), Option(decrExpr))
    val r = verifyStmtModular(methodName, stmt, varsInStmt, pres, posts)

    InvariantTracking.get(firstExistsInv.debugId.get).decrRemovedQuantifier()

    r
  }

  // This generates a method to verify the invariant when using sync, syncTot or forAllExists loop rule
  def translateInvariantVerificationModular(invs: Seq[Expr], normalizedInv: Seq[Expr], loopGuard: Expr, loopBody: CompositeStmt, decrExpr: Option[Expr], rule: String, isAutoSelected: Boolean): Seq[vpr.Method] = {
    val methodName = if (!isAutoSelected) checkInvMethodName + "_" + rule + loopCounter
    else checkInvMethodName + "_" + rule + "_auto" + loopCounter

    val inputStates = SetState.localVar("S0")
    val outputStates = SetState.localVar("SS")
    val inputFailureStates = SetState.localVar("S0_fail")
    val outputFailureStates = SetState.localVar("SS_fail")
    val STmp = SetState.localVar(tempStatesVarName)
    val SFailTmp = SetState.localVar(tempFailedStatesVarName)

    val state = State.localVarDecl(sVarName)
    val s1 = State.localVarDecl(s1VarName)
    val s2 = State.localVarDecl(s2VarName)

    // A logical variable that holds the value of the expression in the decreases clause
    val t = vpr.LocalVar(tVarName + loopCounter, vpr.Int)()
    val tId = Id(tVarName + loopCounter)
    tId.typ = IntType()
    val tDecl = vpr.LocalVarDecl(t.name, t.typ)()

    var methodPres: Seq[vpr.Exp] = Seq.empty
    var methodPosts: Seq[vpr.Exp] = Seq.empty
    var methodArgs: Seq[vpr.LocalVarDecl] = Seq(tDecl)
    var methodBody: Seq[vpr.Stmt] = Seq.empty
    var methodLocalVars: Seq[vpr.LocalVar] = Seq(STmp, SFailTmp)

    methodPres = methodPres :+ getAllInvariantsWithTriggers(normalizedInv, inputStates, inputFailureStates)

    for ((normInv, i) <- normalizedInv.zipWithIndex) {
      val oInv = InvariantTracking.get(normInv.debugId.get).inv
      val qc = InvariantTracking.get(normInv.debugId.get).quantifiersRemoved

      methodPosts = methodPosts :+ translateExp(normInv, null, outputStates, outputFailureStates, info = new Logger(VerificationErrors.LoopInvariant(oInv), Logger.ERR)
        .addTitle("Verification Error")
        .addQuantifiersRemoved(qc)
        .addWhileRule(rule)
        .addOffset((invs(i).offsetLeft, invs(i).offsetRight))
        .toAnnotationInfo())
    }

    if (decrExpr.isDefined) {
      if (rule == "syncRule" || rule == "forAllExistsRule") {
        if (!isAutoSelected) new Logger("Warning: the decreases clause is disgarded by the verifier when syncRule or forAllExistsRule is used", Logger.WARN)
      } else {
        //  t == decrExpr for all states
        val translatedDecr = translateExp(decrExpr.get, state.localVar, inputStates, inputFailureStates)
        val trigger = Seq(vpr.Trigger(Seq(SetState.getInSetApp(Seq(state.localVar, inputStates), useLimited = true)))())
        val decrPre = vpr.Forall(Seq(state), trigger,
          vpr.Implies(SetState.getInSetApp(Seq(state.localVar, inputStates), useLimited = true),
            vpr.EqCmp(translatedDecr, State.get(state.localVar, tId))()
          )())(info = new Logger(VerificationErrors.LoopVariant(decrExpr.get), Logger.ERR)
            .addTitle("Verification Error 2")
            .addOffset((decrExpr.get.offsetLeft, decrExpr.get.offsetRight))
            .toAnnotationInfo())
        methodPres = methodPres :+ decrPre
      }
    }

    val allVars = loopBody.allProgVars.map(v => vpr.LocalVar(v._1, v._2 match {
      case _: StateType => translateType(v._2)
      case _: StmtBlockType => translateType(v._2)
      case _: UnknownType => translateType(v._2)
      case _ => vpr.Int
    })()).toSeq
    val (_, _, otherVars, pre2) = separateVarsByType(allVars :+ t)
    methodArgs = methodArgs ++ allVars.map(v => vpr.LocalVarDecl(v.name, v.typ)())
    methodLocalVars = methodLocalVars ++ otherVars
    methodPres = methodPres ++ pre2

    val trigger = Seq(vpr.Trigger(Seq(SetState.getInSetApp(Seq(state.localVar, outputStates))))())
    val loopGuardHoldsForAll = vpr.Forall(Seq(state), trigger, vpr.Implies(
      SetState.getInSetApp(Seq(state.localVar, outputStates)),
      translateExp(loopGuard, state.localVar, outputStates, outputFailureStates)
    )())()

    val sameGuardValue = vpr.Forall(Seq(s1, s2), Seq.empty, vpr.Implies(
      vpr.And(SetState.getInSetApp(Seq(s1.localVar, outputStates)), SetState.getInSetApp(Seq(s2.localVar, outputStates)))(),
      vpr.EqCmp(translateExp(loopGuard, s1.localVar, outputStates, outputFailureStates), translateExp(loopGuard, s2.localVar, outputStates, outputFailureStates))()
    )())()

    if (rule == "syncRule" || rule == "syncTotRule") {
      if (!isAutoSelected) methodBody = methodBody :+ vpr.Assert(sameGuardValue)(info = new Logger(VerificationErrors.LoopSyncGuard(loopGuard), Logger.ERR)
        .addTitle("Verification Error")
        .addOffset((loopGuard.offsetLeft, loopGuard.offsetRight))
        .toAnnotationInfo())
      methodBody = methodBody :+ vpr.Inhale(loopGuardHoldsForAll)()
    }

    val methodBodyAndVars = {
      if (rule == "forAllExistsRule") {
        val stmtToTranslate = IfElseStmt(loopGuard, loopBody, CompositeStmt(Seq.empty))
        translateStmt(stmtToTranslate, outputStates, outputFailureStates)
      } else translateStmt(loopBody, outputStates, outputFailureStates)
    }

    methodBody = methodBody ++ methodBodyAndVars._1
    methodLocalVars = methodLocalVars ++ methodBodyAndVars._2

    if (!decrExpr.isEmpty && rule != "syncRule" && rule != "forAllExistsRule") {
      val translatedDecr = translateExp(decrExpr.get, state.localVar, outputStates, outputFailureStates)
      // Assert that the current value of decrExpr is in the range of [0, t)
      val decrPost = vpr.Forall(Seq(state), Seq.empty,
        vpr.Implies(SetState.getInSetApp(Seq(state.localVar, outputStates)),
          vpr.And(vpr.GeCmp(translatedDecr, zero)(),
            vpr.LtCmp(translatedDecr, State.get(state.localVar, tId))()
          )()
        )()
      )(info = new Logger(VerificationErrors.LoopVariant(decrExpr.get), Logger.ERR)
        .addTitle("Verification Error 3")
        .addOffset((decrExpr.get.offsetLeft, decrExpr.get.offsetRight))
        .toAnnotationInfo())
      methodPosts = methodPosts :+ decrPost
    }

    val method = createViperMethod(methodName, methodArgs, Seq.empty, methodPres, methodPosts, methodBody, methodLocalVars.map(v => vpr.LocalVarDecl(v.name, v.typ)()))
    Seq(method)
  }

  def translateInvariantVerificationInline(inv: Seq[Expr], loopGuard: Expr, loopBody: CompositeStmt, decrExpr: Option[Expr], currStates: vpr.LocalVar, currFailureStates: vpr.LocalVar, rule: String, isAutoSelected: Boolean): (Seq[vpr.Stmt], Seq[vpr.LocalVar]) = {
    var returnedStmts: Seq[vpr.Stmt] = Seq.empty
    var ifBodyStmts: Seq[vpr.Stmt] = Seq.empty
    val nonDetBool = vpr.LocalVar(nonDetBoolName + loopCounter, vpr.Bool)()
    val state = State.localVarDecl(sVarName)
    val s1 = State.localVarDecl(s1VarName)
    val s2 = State.localVarDecl(s2VarName)
    // A logical variable that holds the value of the expression in the decreases clause
    val t = vpr.LocalVar(tVarName + loopCounter, vpr.Int)()
    val tId = Id(tVarName + loopCounter)
    tId.typ = IntType()
    var returnedVars = Seq(nonDetBool)

    // This only matters when the rule is default
    val currLoopIndexDecl = vpr.LocalVarDecl(currLoopIndexName + loopCounter, vpr.Int)()
    currLoopIndex = currLoopIndexDecl.localVar

    if (rule == "desugaredRule") {
      // Assume loop index $n >= 0
      val havocIndex = havocIntMethodCall(currLoopIndexDecl.localVar)
      val indexNonNeg = vpr.Inhale(vpr.GeCmp(currLoopIndex, zero)())()
      returnedStmts = returnedStmts ++ Seq(havocIndex, indexNonNeg)
      returnedVars = returnedVars :+ currLoopIndexDecl.localVar
    }

    val havocStates = havocSetMethodCall(currStates)
    val havocFailureStates = havocSetMethodCall(currFailureStates)
    val inSetEq = inhaleInSetEqStmt(state, currStates)
    val inSetEqFail = inhaleInSetEqStmt(state, currFailureStates)
    // Assume I(n)
    val inhaleIn = vpr.Inhale(getAllInvariantsWithTriggers(inv, currStates, currFailureStates))()
    ifBodyStmts = ifBodyStmts ++ Seq(havocStates, havocFailureStates, inhaleIn) ++ inSetEq ++ inSetEqFail

    if (!decrExpr.isEmpty) {
      if (rule == "syncRule" || rule == "forAllExistsRule") {
        if (!isAutoSelected) new Logger("Warning: the decreases clause is disgarded by the verifier when syncRule or forAllExistsRule is used", Logger.WARN)
      } else {
        // Inhale t == decrExpr for all states
        val translatedDecr = translateExp(decrExpr.get, state.localVar, currStates, currFailureStates)
        ifBodyStmts = ifBodyStmts :+ vpr.Inhale(vpr.Forall(Seq(state), Seq.empty,
          vpr.Implies(SetState.getInSetApp(Seq(state.localVar, currStates)),
            vpr.EqCmp(translatedDecr, State.get(state.localVar, tId))()
          )())())()
        returnedVars = returnedVars :+ t
      }
    }

    val loopGuardHoldsForAll = vpr.Forall(Seq(state), Seq.empty, vpr.Implies(
      SetState.getInSetApp(Seq(state.localVar, currStates)),
      translateExp(loopGuard, state.localVar, currStates, currFailureStates)
    )())()
    val sameGuardValue = vpr.Forall(Seq(s1, s2), Seq.empty, vpr.Implies(
      vpr.And(SetState.getInSetApp(Seq(s1.localVar, currStates)), SetState.getInSetApp(Seq(s2.localVar, currStates)))(),
      vpr.EqCmp(
        translateExp(loopGuard, s1.localVar, currStates, currFailureStates),
        translateExp(loopGuard, s2.localVar, currStates, currFailureStates))()
    )())()
    if (rule == "syncRule" || rule == "syncTotRule") {
      if (!isAutoSelected) ifBodyStmts = ifBodyStmts :+ vpr.Assert(sameGuardValue)(info = new Logger(VerificationErrors.LoopSyncGuard(loopGuard), Logger.ERR)
        .addTitle("Verification Error")
        .addOffset((loopGuard.offsetLeft, loopGuard.offsetRight))
        .toAnnotationInfo())
      ifBodyStmts = ifBodyStmts :+ vpr.Inhale(loopGuardHoldsForAll)()
    } else if (rule == "desugaredRule") {
      val assumeLoopGuard = translateStmt(AssumeStmt(loopGuard), currStates, currFailureStates)._1
      ifBodyStmts = ifBodyStmts ++ assumeLoopGuard
    }

    val translatedLoopBody = {
      if (rule == "forAllExistsRule") {
        val stmtToTranslate = IfElseStmt(loopGuard, loopBody, CompositeStmt(Seq.empty))
        translateStmt(stmtToTranslate, currStates, currFailureStates)
      } else translateStmt(loopBody, currStates, currFailureStates)
    }
    ifBodyStmts = ifBodyStmts ++ translatedLoopBody._1
    returnedVars = returnedVars ++ translatedLoopBody._2

    // Update loop index to be $n + 1 (Note that this only matters when the rule is default)
    currLoopIndex = vpr.Add(currLoopIndexDecl.localVar, one)()
    val assertIs = inv.map { i =>
      vpr.Assert(translateExp(i, null, currStates, currFailureStates))(info = new Logger(VerificationErrors.Deprecated(i), Logger.ERR)
        .addTitle("Verification Error")
        .addOffset((i.offsetLeft, i.offsetRight))
        .toAnnotationInfo())
    }
    ifBodyStmts = ifBodyStmts ++ assertIs

    if (decrExpr.isDefined && rule != "syncRule" && rule != "forAllExistsRule") {
      val translatedDecr = translateExp(decrExpr.get, state.localVar, currStates, currFailureStates)
      // Assert that the current value of decrExpr is in the range of [0, t)
      val tf_decr_exp = vpr.Forall(Seq(state), Seq.empty, vpr.Implies(SetState.getInSetApp(Seq(state.localVar, currStates)), vpr.And(vpr.GeCmp(translatedDecr, zero)(), vpr.LtCmp(translatedDecr, State.get(state.localVar, tId))())())())()
      val assert_variant = vpr.Assert(tf_decr_exp)(info = new Logger(VerificationErrors.LoopVariant(decrExpr.get), Logger.ERR)
        .addTitle("Verification Error 4")
        .addOffset((decrExpr.get.offsetLeft, decrExpr.get.offsetRight))
        .toAnnotationInfo())
      ifBodyStmts = ifBodyStmts :+ assert_variant
    }

    ifBodyStmts = ifBodyStmts :+ vpr.Inhale(falseLit)()

    val ifStmt = vpr.If(nonDetBool, vpr.Seqn(ifBodyStmts, Seq.empty)(), vpr.Seqn(Seq.empty, Seq.empty)())()
    returnedStmts = returnedStmts :+ ifStmt

    (returnedStmts, returnedVars)
  }

  // Returns an alias that is formed by appending a $ to v's identifier
  def getAliasForProofVar(v: ProofVar): vpr.LocalVarDecl = {
    if (!useAliasForProofVar) throw UnknownException("Method getAliasForProofVar cannot be called when assertProofVar == false")
    vpr.LocalVarDecl("$" + v.name, translateType(v.typ))()
  }

  def inhaleInSetEqStmt(state: vpr.LocalVarDecl, currStates: vpr.LocalVar): Seq[vpr.Inhale] = {
    val unlimited = vpr.Inhale(vpr.Forall(
      Seq(state),
      Seq.empty,
      vpr.EqCmp(SetState.getInSetApp(Seq(state.localVar, currStates)),
        SetState.getInSetApp(Seq(state.localVar, currStates), false)
      )()
    )()
    )()

    val limited = vpr.Inhale(vpr.Forall(
      Seq(state),
      Seq.empty,
      vpr.EqCmp(SetState.getInSetApp(Seq(state.localVar, currStates), useLimited=true),
        SetState.getInSetApp(Seq(state.localVar, currStates), false, useLimited=true)
      )()
    )()
    )()
    Seq(unlimited, limited)
  }

  // Note that second argument, state, is only used to translate id
  def translateExp(e: Expr, state: vpr.LocalVar, currStates: vpr.Exp, failureStates: vpr.Exp, info: Info = NoInfo): vpr.Exp = {
    e match {
      case id@Id(_) => State.get(state, id)
      case Num(value) => vpr.IntLit(value)(info = info)
      case BoolLit(value) => vpr.BoolLit(value)(info = info)
      case BinaryExpr(left, op, right) =>
        op match {
          case "+" => vpr.Add(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "-" => vpr.Sub(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "*" => vpr.Mul(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "/" => vpr.Div(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "%" => vpr.Mod(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "&&" => vpr.And(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "||" => vpr.Or(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "==" => vpr.EqCmp(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "!=" => vpr.NeCmp(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case ">" => vpr.GtCmp(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case ">=" => vpr.GeCmp(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "<" => vpr.LtCmp(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
          case "<=" => vpr.LeCmp(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
        }
      case exp@UnaryExpr(op, e) =>
        op match {
          case "!" => { vpr.Not(translateExp(e, state, currStates, failureStates))(info = info)}
          case "-" => vpr.Minus(translateExp(e, state, currStates, failureStates))(info = info)
        }
      case av@AssertVar(name) =>
        vpr.LocalVar(name, translateType(av.typ))(info = info)
      case a@Assertion(quantifier, vars, body) =>
        // if (!hintDecl.isEmpty) translateHintDecl(hintDecl)
        val variables = vars.map(v => translateAssertVarDecl(v))
        if (quantifier == "forall") {
          val triggers = if (needTriggers) {
            a.triggers.map(seq => {
              vpr.Trigger(seq.map(s => translateExp(s, state, currStates, failureStates)))(info = info)
            })
          } else Seq.empty
          vpr.Forall(variables, triggers, translateExp(body, state, currStates, failureStates))(info = info)
        } else if (quantifier == "exists") {
          if (isPostcondition && !postIsTopExists) postIsTopExists = a.topExists
          vpr.Exists(variables, Seq.empty, translateExp(body, state, currStates, failureStates))(info = info)
        }
        else throw UnknownException("Unexpected quantifier " + quantifier)
      case ImpliesExpr(left, right) =>
        vpr.Implies(translateExp(left, state, currStates, failureStates), translateExp(right, state, currStates, failureStates))(info = info)
      case se@StateExistsExpr(s, err) =>
        val translatedState = translateExp(s, state, currStates, failureStates)
        if (err) SetState.getInSetApp(Seq(translatedState, failureStates), se.useForAll, se.useLimited && needTriggers)
        else SetState.getInSetApp(Seq(translatedState, currStates), se.useForAll, se.useLimited && needTriggers)
      case LoopIndex() => currLoopIndex
      case pv@ProofVar(name) =>
        if (useAliasForProofVar && currProofVarName==name) getAliasForProofVar(pv).localVar
        else vpr.LocalVar(name, translateType(pv.typ))(info = info)
      case Hint(name, arg) =>
        containsHints = true
        if (removeHints) trueLit
        else
          // When a hint is used, always call the function named as name + hintWrapperSuffix
          vpr.FuncApp(name + hintWrapperSuffix, Seq(translateExp(arg, state, currStates, failureStates)))(vpr.NoPosition, info, vpr.Bool, vpr.NoTrafos)
      // case HintDecl(name, args) => This is translated in a separate method
      // case AssertVarDecl(vName, vType) => This is translated in a separate method below, as vpr.LocalVarDecl is of type Stmt
      case e@SeqAssignExpr(elems) => HHLSeq.create(elems.map(el => translateExp(el, state, currStates, failureStates, info)), translateType(e.typ.asInstanceOf[SeqType].sType))
      case e@SetAssignExpr(elems) =>
        if (elems.isEmpty) vpr.EmptySet(translateType(e.typ.asInstanceOf[SetType].sType))()
        else vpr.ExplicitSet(elems.map(el => translateExp(el, state, currStates, failureStates, info)))()
      case e@MapAssignExpr(elems) =>
        HHLMap.create(elems.map(mExp => (
          translateExp(mExp.k, state, currStates, failureStates, info),
          translateExp(mExp.v, state, currStates, failureStates, info)
        )), translateType(e.typ.asInstanceOf[MapType].kType), translateType(e.typ.asInstanceOf[MapType].vType))
      case e@LookupExpr(base, id) =>
        if (e.baseType.isInstanceOf[SeqType]) {
          HHLSeq.lookUp(
            translateExp(base, state, currStates, failureStates, info),
            translateExp(id, state, currStates, failureStates, info),
            translateType(base.typ.asInstanceOf[SeqType].sType)
          )
        } else if (e.baseType.isInstanceOf[MapType]) {
          HHLMap.lookUp(
            translateExp(base, state, currStates, failureStates, info),
            translateExp(id, state, currStates, failureStates, info),
            translateType(base.typ.asInstanceOf[MapType].kType),
            translateType(base.typ.asInstanceOf[MapType].vType)
          )
        } else {
          val stateVar = translateExp(base, state, currStates, failureStates)
          translateExp(id, stateVar.asInstanceOf[vpr.LocalVar], currStates, failureStates, info = info)
        }

      case e@LengthExpr(id) =>
        val tId = translateExp(id, state, currStates, failureStates, info)
        id.typ match {
          case seq: SeqType => HHLSeq.length(tId, translateType(seq.sType))
          case _: SetType => vpr.AnySetCardinality(tId)()
          case map: MapType => HHLMap.cardinality(tId, translateType(map.kType), translateType(map.vType))
        }

      case e@CombExpr(lhs, rhs, op) =>
        val translatedLhs = translateExp(lhs, state, currStates, failureStates, info)
        val translatedRhs = translateExp(rhs, state, currStates, failureStates, info)

        op match {
          case "union" =>
            vpr.AnySetUnion(translatedLhs, translatedRhs)()
          case "intersection" =>
            vpr.AnySetIntersection(translatedLhs, translatedRhs)()
          case "setminus" =>
            vpr.AnySetMinus(translatedLhs, translatedRhs)()
          case "in" =>
            if (rhs.typ.isInstanceOf[SetType]) vpr.AnySetContains(translatedLhs, translatedRhs)()
            else {
              val kType = translateType(rhs.typ.asInstanceOf[MapType].kType)
              val vType = translateType(rhs.typ.asInstanceOf[MapType].vType)

              val mapDomain = HHLMap.domain(translatedRhs, kType, vType)
              vpr.AnySetContains(translatedLhs, mapDomain)()
            }
          case "++" =>
            HHLSeq.append(translatedLhs, translatedRhs, translateType(lhs.typ.asInstanceOf[SeqType].sType))
          case _ =>
            throw UnknownException("Unknown operator detected while translating expression!")
        }
      case e@UpdateMapExpr(map, mExp) =>
        HHLMap.update(
          translateExp(map, state, currStates, failureStates, info),
          translateExp(mExp.k, state, currStates, failureStates, info),
          translateExp(mExp.v, state, currStates, failureStates, info),
          translateType(map.typ.asInstanceOf[MapType].kType),
          translateType(map.typ.asInstanceOf[MapType].vType)
        )
      case _ =>
        throw UnknownException("Unexpected expression " + e + " with class " + e.getClass())
    }
  }

  def translateHintDecl(decl: HintDecl, arg: vpr.Exp): vpr.Exp = {
    if (verifierOption == 0) throw UnknownException("Hints cannot be declared when using forall-HHL")
    // Generate 2 Viper functions for the hint declaration
    // 1. A function named as decl.name where body is an expression that evaluates to true
    // 2. A function named as decl.name + hintWrapperSuffix where body is a call to the function above
    // The second function is needed when the hint is used in the postcondition
    val k = vpr.LocalVarDecl(kVarName, vpr.Int)()

    val allFuncsNames = allFuncs.map(f => f.name)
    if (!allFuncsNames.contains(decl.name)) {
      // Function 1
      val hintFuncBody = vpr.Or(vpr.LeCmp(k.localVar, zero)(), vpr.GtCmp(k.localVar, zero)())()
      val hintFunc = vpr.Function(decl.name, Seq(k),
        vpr.Bool, Seq.empty, Seq.empty, Option(hintFuncBody))()

      // Function 2
      val hintWrapperBody = vpr.FuncApp(decl.name, Seq(k.localVar))(vpr.NoPosition, vpr.NoInfo, vpr.Bool, vpr.NoTrafos)
      val hintWrapperFunc = vpr.Function(decl.name + hintWrapperSuffix, Seq(k), vpr.Bool, Seq.empty, Seq.empty, Option(hintWrapperBody))()

      allFuncs = allFuncs ++ Seq(hintFunc, hintWrapperFunc)
    }

    vpr.FuncApp(decl.name, Seq(arg))(vpr.NoPosition, vpr.NoInfo, vpr.Bool, vpr.NoTrafos)
  }

  def translateAssertVarDecl(decl: AssertVarDecl): vpr.LocalVarDecl = {
    vpr.LocalVarDecl(decl.vName.name, translateType(decl.vType))()
  }

  // This returns a Viper assume statement that expresses the following:
  // assume forall stateVar :: in_set(state1, S1) ==> (exists state2 :: in_set(state2, S2) && equal_on_everything_except(state1, state2, varToHavoc) && extraExp)
  def translateHavocVarHelper(S1: vpr.LocalVar, S2: vpr.LocalVar, state1: vpr.LocalVar, state2: vpr.LocalVar,
                              varToHavoc: vpr.LocalVarDecl, extraExp: vpr.Exp = null, extraVar: vpr.LocalVarDecl = null, triggers: Seq[vpr.Trigger] = Seq.empty, useForAll: Boolean = true) : vpr.Inhale = {
    var itemsInExistsExpr: Seq[vpr.Exp] = Seq(SetState.getInSetApp(Seq(state2, S2), useForAll),
      State.getEqualExceptApp(Seq(state1, state2, varToHavoc.localVar)))
    if (extraExp != null) itemsInExistsExpr = itemsInExistsExpr :+ extraExp
    val existsExpr = vpr.Exists(Seq(vpr.LocalVarDecl(state2.name, state2.typ)()), Seq.empty, getAndOfExps(itemsInExistsExpr))()
    translateAssumeWithViperExpr(state1, S1, existsExpr, extraVarDecl=extraVar, triggers=triggers, useForAll=useForAll)
  }

  // This returns a Viper assume statement of the form "assume forall state (, extraVar) :: in_set(state, S) (&& leftExp) => (rightExp)"
  // T is determined by the typVarMap(T -> someType)
  def translateAssumeWithViperExpr(state: vpr.LocalVar, S: vpr.LocalVar, rightExp: vpr.Exp,
                                   leftExp: vpr.Exp = null, extraVarDecl: vpr.LocalVarDecl = null, triggers: Seq[vpr.Trigger] = Seq.empty, useForAll: Boolean = true) : vpr.Inhale = {
    val lhs = {
      val inSetExp = SetState.getInSetApp(Seq(state, S), useForAll)
      if (leftExp != null) vpr.And(inSetExp, leftExp)()
      else inSetExp
    }
    val stateDecl = vpr.LocalVarDecl(state.name, state.typ)()
    val vars = if (extraVarDecl != null) Seq(stateDecl, extraVarDecl) else Seq(stateDecl)
    vpr.Inhale(
      vpr.Forall(
        vars,
        triggers,
        vpr.Implies(
          lhs, rightExp
        )()
      )()
    )()
  }

  def generatePreamble(): (Seq[vpr.Domain], Seq[vpr.Method]) = {
    // Create domains
    var domains = Seq(
      State.domain(TypeChecker.declaredTypes),
      SetState.domain()
    )
    if (TypeChecker.hasSeqs) domains = domains ++ HHLSeq.domains
    if (TypeChecker.hasMaps) domains = domains ++ HHLMap.domains

    // Create additional methods
    val SS = SetState.localVarDecl("SS")
    val k = vpr.LocalVarDecl(kVarName, vpr.Int)()
    val methods = Seq(
      vpr.Method(havocSetMethodName, Seq.empty, Seq(SS), Seq.empty, Seq.empty, Option.empty)(),
      vpr.Method(havocIntMethodName, Seq.empty, Seq(k), Seq.empty, Seq.empty, Option.empty)()
    )

    (domains, methods)
  }

  // Connects all expressions in the input with "&&"
  def getAndOfExps(exps: Seq[vpr.Exp]): vpr.Exp = {
    if (exps.isEmpty) throw UnknownException("The input to getAndOfExps cannot be an empty sequence")
    exps.reduceLeft((e1, e2) => vpr.And(e1, e2)())
  }

  def havocSetMethodCall(set: vpr.LocalVar): vpr.MethodCall = {
    vpr.MethodCall(havocSetMethodName, Seq.empty, Seq(set))(pos = vpr.NoPosition, info = vpr.NoInfo, errT = vpr.NoTrafos)
  }

  def havocIntMethodCall(i: vpr.LocalVar): vpr.MethodCall = {
    vpr.MethodCall(havocIntMethodName, Seq.empty, Seq(i))(pos = vpr.NoPosition, info = vpr.NoInfo, errT = vpr.NoTrafos)
  }

  // translate type to vpr type
  def translateType(typ: Type): vpr.Type = {
    // println("translating type:" + typ)
    typ match {
      case t: IntType => vpr.Int
      case t: BoolType => vpr.Bool
      case t: SeqType => HHLSeq.domainType(translateType(t.sType))
      case t: SetType => vpr.SetType(translateType(t.sType))
      case t: MapType => HHLMap.domainType(translateType(t.kType), translateType(t.vType))
      case StateType() => State.stateType
      case _ =>
        throw UnknownException("Cannot translate type " + typ)
    }
  }

  def translateMethodVariables(params: Seq[Id]): Seq[vpr.LocalVarDecl] = params.map(id => vpr.LocalVarDecl(id.name, vpr.Int)())

  def getVprVar(name: String): vpr.LocalVar = vpr.LocalVar(name, vpr.Int)()
}
