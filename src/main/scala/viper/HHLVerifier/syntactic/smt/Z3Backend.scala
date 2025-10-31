package viper.HHLVerifier.syntactic.smt

import com.microsoft.z3._
import viper.HHLVerifier.Main
import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.{SyntacticEngine, WeakestPrecondition}
import viper.HHLVerifier.typing._

import scala.collection.mutable

class Z3Backend extends SMTBackend {
  /** Z3 context used to construct sorts, expressions and solvers. */
  private val ctx: Context = new Context()

  private val IntSort: Sort  = ctx.getIntSort
  private val BoolSort: Sort = ctx.getBoolSort

  /** Sort that represents a ''program state'': An array from variable
   * indices to their value in this state. */
  private val StateSort: Sort = ctx.mkArraySort(IntSort, IntSort)

  /** Fresh Z3 constant of sort [[SetSort]] that denotes the abstract set '''S'''.
   * Cf. HHL paper, definition 3.
   * New: Instead of an array using a function to represent the set of program states
   */
  private val S: FuncDecl[BoolSort] = ctx.mkFuncDecl("S", StateSort, BoolSort.asInstanceOf[BoolSort])

  /**
   * Fresh Z3 constant of sort [[SetSort]] that denotes the abstract set tracking error states.
   * Cf. Hypra paper, definition 1.
   */
  private val S_err: FuncDecl[BoolSort] = ctx.mkFuncDecl("S_err", StateSort, BoolSort.asInstanceOf[BoolSort])

  /** Environment that maps program variable names and logical variable names to their Z3 integer constants.
   * Populated on the fly when encountering program variables in hyper-assertions. */
  private val progEnv: mutable.Map[String, IntExpr] = mutable.Map.empty[String, IntExpr]

  /** Environment that maps state variable names (introduced by quantifiers) to Z3
   * array constants of sort [[StateSort]]. Populated on the fly when encountering state variables in hyper-assertions. */
  private val stateEnv: mutable.Map[String, ArrayExpr[IntSort, IntSort]] = mutable.Map.empty[String, ArrayExpr[IntSort, IntSort]]

  def addToGlobalSMTPool(pre: viper.HHLVerifier.ast.Expr, wp: viper.HHLVerifier.ast.Expr): Unit = {
    val z3Pre = encodeBool(WeakestPrecondition.desugarQuantifiers(pre))
    val z3WP = encodeBool(WeakestPrecondition.desugarQuantifiers(wp))
    val translatedImp = ctx.mkImplies(z3Pre, z3WP).translate(SyntacticEngine.exportCtx).asInstanceOf[BoolExpr]
    SyntacticEngine.addConstraint(translatedImp)
  }

  def generateSingleSMTEncoding(pre: viper.HHLVerifier.ast.Expr, wp: viper.HHLVerifier.ast.Expr): String = {
    val z3Pre = encodeBool(WeakestPrecondition.desugarQuantifiers(pre))
    val z3WP = encodeBool(WeakestPrecondition.desugarQuantifiers(wp))

    val solver = ctx.mkSolver()
    val p = ctx.mkParams()
    p.add("timeout", Main.smtSolverTimeLimitMs)
    solver.setParameters(p)

    val negImp = ctx.mkNot(ctx.mkImplies(z3Pre, z3WP))
    solver.add(negImp)

    val sb = new StringBuilder
    sb.append("(set-logic ALL)\n") // for CVC5
    sb.append(solver.toString)
    sb.append("\n(check-sat)\n(exit)\n")
    sb.toString
  }

  def checkEntailment(pre: viper.HHLVerifier.ast.Expr, wp: viper.HHLVerifier.ast.Expr, usedForEval: Boolean = false): SMTStatus = {
    // encode the precondition and WP
    val z3Pre = encodeBool(WeakestPrecondition.desugarQuantifiers(pre))
    val z3WP = encodeBool(WeakestPrecondition.desugarQuantifiers(wp))
    val z3FinalFormula = ctx.mkNot(ctx.mkImplies(z3Pre, z3WP))

    if (usedForEval) Main.timeStamps(3) = Main.timeStamps(3).appended(System.nanoTime()) // timestamp after SMT encoding

    // solve ¬(pre ⇒ wp)
    val solver = ctx.mkSolver(/*"AUFLIA"*/)
    val p = ctx.mkParams()
    p.add("timeout", Main.smtSolverTimeLimitMs)
    solver.setParameters(p)
    solver.add(z3FinalFormula)

    val result = solver.check()
    if (Main.debugLogsActive && result == Status.UNKNOWN) println("\tReason for unknown: " + solver.getReasonUnknown)
    result match {
      case Status.SATISFIABLE => SMTStatus.Satisfiable
      case Status.UNSATISFIABLE => SMTStatus.Unsatisfiable
      case Status.UNKNOWN => SMTStatus.Unknown
    }
  }

  private def encodeBool(expr: viper.HHLVerifier.ast.Expr): BoolExpr = expr match {
    case BoolLit(value) => ctx.mkBool(value)
    case BinaryExpr(e1, op, e2) => op match {
      case "&&" => ctx.mkAnd(encodeBool(e1), encodeBool(e2))
      case "||" => ctx.mkOr(encodeBool(e1), encodeBool(e2))
      case "==" => ctx.mkEq(encodeInt(e1), encodeInt(e2))
      case "!=" => ctx.mkDistinct(encodeInt(e1), encodeInt(e2))
      case ">=" => ctx.mkGe(encodeInt(e1), encodeInt(e2))
      case "<=" => ctx.mkLe(encodeInt(e1), encodeInt(e2))
      case ">" => ctx.mkGt(encodeInt(e1), encodeInt(e2))
      case "<" => ctx.mkLt(encodeInt(e1), encodeInt(e2))
    }
    case UnaryExpr("!", e) => ctx.mkNot(encodeBool(e))
    case ImpliesExpr(left, right) => ctx.mkImplies(encodeBool(left), encodeBool(right))
    case Assertion(quantifier, List(AssertVarDecl(vName, StateType())), body) => {
      val constantsArray: Array[com.microsoft.z3.Expr[_]] = Array(getStateEnv(vName.name))
      val encodedBody: com.microsoft.z3.BoolExpr = encodeBool(body)
      quantifier match {
        case "exists" => ctx.mkExists(constantsArray, encodedBody, 0, null, null, null, null)
        case "forall" => ctx.mkForall(constantsArray, encodedBody, 0, null, null, null, null)
      }
    }
    case Assertion(quantifier, List(AssertVarDecl(vName, _)), body) => { // quantifier over non-state variable
      val constantsArray: Array[com.microsoft.z3.Expr[_]] = Array(getProgEnv(vName.name))
      val encodedBody: com.microsoft.z3.BoolExpr = encodeBool(body)
      quantifier match {
        case "exists" => ctx.mkExists(constantsArray, encodedBody, 0, null, null, null, null)
        case "forall" => ctx.mkForall(constantsArray, encodedBody, 0, null, null, null, null)
      }
    }
    case LookupExpr(AssertVar(stateName), Id(varName)) => sys.error("LogicEncoder: Unexpected LookupExpr in boolean conversion: " + expr.toString)
    case LookupExpr(id, index) => encodeBool(ParallelRunner.resolveLookup(index)(id.asInstanceOf[AssertVar]))
    case StateExistsExpr(AssertVar(name), false) => ctx.mkApp(S, getStateEnv(name)).asInstanceOf[BoolExpr] // non-error state
    case StateExistsExpr(AssertVar(name), true) => ctx.mkApp(S_err, getStateEnv(name)).asInstanceOf[BoolExpr] // error states
    case _ => sys.error("LogicEncoder: Unexpected expression in boolean conversion: " + expr.toString)
  }

  private def encodeInt(expr: viper.HHLVerifier.ast.Expr): IntExpr = expr match {
    case LookupExpr(AssertVar(stateName), Id(varName)) => ctx.mkSelect(getStateEnv(stateName), getProgEnv(varName)).asInstanceOf[IntExpr]
    case LookupExpr(id, index) => encodeInt(ParallelRunner.resolveLookup(index)(id.asInstanceOf[AssertVar]))
    case Id(name) => getProgEnv(name) // a program variable shouldn't occur outside of a LookupExpr. However, there can be free variables from the exists rule
    case Num(value) => ctx.mkInt(value)
    case AssertVar(name) => getProgEnv(name)
    case BinaryExpr(e1, op, e2) => op match {
      case "+" => ctx.mkAdd(encodeInt(e1), encodeInt(e2)).asInstanceOf[IntExpr]
      case "-" => ctx.mkSub(encodeInt(e1), encodeInt(e2)).asInstanceOf[IntExpr]
      case "*" => ctx.mkMul(encodeInt(e1), encodeInt(e2)).asInstanceOf[IntExpr]
      case "/" => ctx.mkDiv(encodeInt(e1), encodeInt(e2)).asInstanceOf[IntExpr]
      case "%" => ctx.mkMod(encodeInt(e1), encodeInt(e2))
    }
    case UnaryExpr("-", e) => ctx.mkUnaryMinus(encodeInt(e)).asInstanceOf[IntExpr]
    case _ => sys.error("LogicEncoder: Unexpected expression in integer conversion: " + expr.toString)
  }

  private def getProgEnv(s: String): com.microsoft.z3.IntExpr = {
    progEnv.getOrElseUpdate(s, ctx.mkIntConst(s))
  }

  private def getStateEnv(s: String): com.microsoft.z3.ArrayExpr[IntSort, IntSort] = {
    stateEnv.getOrElseUpdate(s, ctx.mkConst(s, StateSort).asInstanceOf[ArrayExpr[IntSort, IntSort]])
  }
}
