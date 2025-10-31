package viper.HHLVerifier.syntactic.smt

import io.github.cvc5._
import viper.HHLVerifier.Main
import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.WeakestPrecondition
import viper.HHLVerifier.typing._

import scala.collection.mutable

class CVC5Backend extends SMTBackend {
  private val tm = new TermManager()
  private val solver = new Solver(tm)

  private val IntSort = tm.getIntegerSort
  private val BoolSort = tm.getBooleanSort
  private val StateSort = tm.mkArraySort(IntSort, IntSort)

  private val SFunSort = tm.mkFunctionSort(StateSort, BoolSort)
  private val S = tm.mkConst(SFunSort, "S")
  private val S_err = tm.mkConst(SFunSort, "S_err")

  private val constEnv: mutable.Map[String, Term] = mutable.Map.empty[String, Term]
  private val stateEnv: mutable.Map[String, Term] = mutable.Map.empty[String, Term] // for free states resulting from some loop rules

  private case class VarEnv(stateVars: Map[String, Term], intVars: Map[String, Term]) {
    def withState(name: String): (VarEnv, Term) = {
      val newVar = tm.mkVar(StateSort, name)
      (copy(stateVars = stateVars + (name -> newVar)), newVar)
    }
    def withInt(name: String): (VarEnv, Term) = {
      val newVar = tm.mkVar(IntSort, name)
      (copy(intVars = intVars + (name -> newVar)), newVar)
    }
    def getState(name: String): Term = stateVars.getOrElse(name, stateEnv.getOrElseUpdate(name, tm.mkConst(StateSort, name + "_const"))) // some loop rules have free states, which need to be treated as constants
    def getInt(name: String): Term = intVars.getOrElse(name, sys.error(s"CVC5Backend: Unbound integer variable '$name'"))
  }
  private object VarEnv {
    def empty: VarEnv = VarEnv(Map.empty, Map.empty)
  }

  private def getConstEnv(s: String): Term = {
    //println("const: " + s)
    //System.out.flush()
    constEnv.getOrElseUpdate(s, tm.mkConst(IntSort, s))
  }

  def checkEntailment(pre: viper.HHLVerifier.ast.Expr, wp: viper.HHLVerifier.ast.Expr, usedForEval: Boolean = false): SMTStatus = {
    val cvc5Pre = encodeBool(WeakestPrecondition.desugarQuantifiers(pre))(VarEnv.empty)
    val cvc5WP = encodeBool(WeakestPrecondition.desugarQuantifiers(wp))(VarEnv.empty)
    val cvc5FinalFormula = tm.mkTerm(Kind.NOT, tm.mkTerm(Kind.IMPLIES, cvc5Pre, cvc5WP))

    if (usedForEval) Main.timeStamps(3) = Main.timeStamps(3).appended(System.nanoTime()) // timestamp after SMT encoding

    // solve ¬(pre ⇒ wp)
    solver.setOption("tlimit-per", Main.smtSolverTimeLimitMs.toString)
    solver.setLogic("ALL")
    //solver.setOption("output-language", "smt2")
    //solver.setOption("output", "pre-asserts")
    solver.assertFormula(cvc5FinalFormula)
    val result = solver.checkSat()

    if (result.isSat) SMTStatus.Satisfiable
    else if (result.isUnsat) SMTStatus.Unsatisfiable
    else SMTStatus.Unknown
  }

  private def encodeBool(expr: Expr)(implicit env: VarEnv): Term = expr match {
    case BoolLit(value) => if (value) tm.mkTrue() else tm.mkFalse()
    case BinaryExpr(e1, op, e2) => op match {
      case "&&" => tm.mkTerm(Kind.AND, encodeBool(e1), encodeBool(e2))
      case "||" => tm.mkTerm(Kind.OR, encodeBool(e1), encodeBool(e2))
      case "==" => tm.mkTerm(Kind.EQUAL, encodeInt(e1), encodeInt(e2))
      case "!=" => tm.mkTerm(Kind.DISTINCT, encodeInt(e1), encodeInt(e2))
      case ">=" => tm.mkTerm(Kind.GEQ, encodeInt(e1), encodeInt(e2))
      case "<=" => tm.mkTerm(Kind.LEQ, encodeInt(e1), encodeInt(e2))
      case ">" => tm.mkTerm(Kind.GT, encodeInt(e1), encodeInt(e2))
      case "<" => tm.mkTerm(Kind.LT, encodeInt(e1), encodeInt(e2))
    }
    case UnaryExpr("!", e) => tm.mkTerm(Kind.NOT, encodeBool(e))
    case ImpliesExpr(left, right) => tm.mkTerm(Kind.IMPLIES, encodeBool(left), encodeBool(right))
    // quantifier over state variable
    case Assertion(quantifier, List(AssertVarDecl(vName, StateType())), body) => {
      val newEnvAndVar = env.withState(vName.name)
      val varList = tm.mkTerm(Kind.VARIABLE_LIST, newEnvAndVar._2)
      val q = quantifier match {
        case "exists" => Kind.EXISTS
        case "forall" => Kind.FORALL
      }
      tm.mkTerm(q, varList, encodeBool(body)(newEnvAndVar._1))
    }
    // quantifier over non-state variable
    case Assertion(quantifier, List(AssertVarDecl(vName, _)), body) => {
      val newEnvAndVar = env.withInt(vName.name)
      val varList = tm.mkTerm(Kind.VARIABLE_LIST, newEnvAndVar._2)
      val q = quantifier match {
        case "exists" => Kind.EXISTS
        case "forall" => Kind.FORALL
      }
      tm.mkTerm(q, varList, encodeBool(body)(newEnvAndVar._1))
    }
    case LookupExpr(AssertVar(_), Id(_)) => sys.error("CVC5Backend: Unexpected LookupExpr in boolean conversion: " + expr.toString)
    case LookupExpr(id, index) => encodeBool(ParallelRunner.resolveLookup(index)(id.asInstanceOf[AssertVar]))
    case StateExistsExpr(AssertVar(name), false) => tm.mkTerm(Kind.APPLY_UF, S, env.getState(name))
    case StateExistsExpr(AssertVar(name), true) => tm.mkTerm(Kind.APPLY_UF, S_err, env.getState(name))
    case _ => sys.error("CVC5Backend: Unexpected expression in boolean conversion: " + expr.toString)
  }

  private def encodeInt(expr: Expr)(implicit env: VarEnv): Term = expr match {
    case LookupExpr(AssertVar(stateName), Id(varName)) => tm.mkTerm(Kind.SELECT, env.getState(stateName), getConstEnv(varName))
    case LookupExpr(id, index) => encodeInt(ParallelRunner.resolveLookup(index)(id.asInstanceOf[AssertVar]))
    case Id(name) => getConstEnv(name)
    case Num(value) => tm.mkInteger(value)
    case AssertVar(name) => env.getInt(name)
    case BinaryExpr(e1, op, e2) => {
      val kind = op match {
        case "+" => Kind.ADD
        case "-" => Kind.SUB
        case "*" => Kind.MULT
        case "/" => Kind.INTS_DIVISION
        case "%" => Kind.INTS_MODULUS
      }
      tm.mkTerm(kind, encodeInt(e1), encodeInt(e2))
    }
    case UnaryExpr("-", e) => tm.mkTerm(Kind.NEG, encodeInt(e))
    case _ => sys.error("CVC5Backend: Unexpected expression in integer conversion: " + expr.toString)
  }
}
