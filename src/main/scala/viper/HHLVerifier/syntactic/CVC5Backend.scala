package viper.HHLVerifier.syntactic

import io.github.cvc5._

import scala.collection.mutable
import viper.HHLVerifier.ast._
import viper.HHLVerifier.typing._

class CVC5Backend {
  private val tm = new TermManager()
  private val solver = new Solver(tm)

  private val IntSort = tm.getIntegerSort
  private val BoolSort = tm.getBooleanSort
  private val StateSort = tm.mkArraySort(IntSort, IntSort)

  private val SFunSort = tm.mkFunctionSort(StateSort, BoolSort)
  private val S = tm.mkConst(SFunSort, "S")

  private val constEnv: mutable.Map[String, Term] = mutable.Map.empty[String, Term]
  private val varEnv: mutable.Map[String, Term] = mutable.Map.empty[String, Term]

  private def getConstEnv(s: String): Term = {
    constEnv.getOrElseUpdate(s, tm.mkConst(IntSort, s))
  }

  private def getVarEnv(s: String, state: Boolean): Term = {
    varEnv.getOrElseUpdate(s, tm.mkConst(if(state) StateSort else IntSort, s))
  }

  private def encodeBool(expr: Expr): Term = expr match {
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
      val varList = tm.mkTerm(Kind.VARIABLE_LIST, getVarEnv(vName.name, state = true))
      val q = quantifier match {
        case "exists" => Kind.EXISTS
        case "forall" => Kind.FORALL
      }
      tm.mkTerm(q, varList, encodeBool(body))
    }
    // quantifier over non-state variable
    case Assertion(quantifier, List(AssertVarDecl(vName, _)), body) => {
      val varList = tm.mkTerm(Kind.VARIABLE_LIST, getVarEnv(vName.name, state = false))
      val q = quantifier match {
        case "exists" => Kind.EXISTS
        case "forall" => Kind.FORALL
      }
      tm.mkTerm(q, varList, encodeBool(body))
    }
    case LookupExpr(AssertVar(_), Id(_)) => sys.error("LogicEncoder: Unexpected LookupExpr in boolean conversion: " + expr.toString)
    case LookupExpr(id, index) => encodeBool(LogicEncoderNew.resolveLookup(index)(id.asInstanceOf[AssertVar]))
    case StateExistsExpr(AssertVar(name), _) => tm.mkTerm(Kind.APPLY_UF, S, getVarEnv(name, state = true))
    case _ => sys.error("CVC5Backend: Unexpected expression in boolean conversion: " + expr.toString)
  }

  private def encodeInt(expr: Expr): Term = expr match {
    case LookupExpr(AssertVar(stateName), Id(varName)) => tm.mkTerm(Kind.SELECT, getVarEnv(stateName, state = true), getConstEnv(varName))
    case LookupExpr(id, index) => encodeInt(LogicEncoderNew.resolveLookup(index)(id.asInstanceOf[AssertVar]))
    case Id(name) => getVarEnv(name, state = false)
    case Num(value) => tm.mkInteger(value)
    case AssertVar(name) => getVarEnv(name, state = false)
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
