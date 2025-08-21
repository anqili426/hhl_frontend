package viper.HHLVerifier.syntactic

import com.microsoft.z3._
import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.WeakestPrecondition
import viper.HHLVerifier.typing._

import scala.collection.mutable

class LogicEncoderNew {

  /** Z3 context used to construct sorts, expressions and solvers. */
  private val ctx: Context = new Context()

  private val IntSort: Sort  = ctx.getIntSort
  private val BoolSort: Sort = ctx.getBoolSort

  /** Sort that represents a ''program state'': An array from variable
   * indices to their value in this state. */
  private val StateSort: Sort = ctx.mkArraySort(IntSort, IntSort)

  /** Sort that represents a ''set of program states'': An array from
   * [[StateSort]] to a boolean membership flag. Usually, we only need
   * one object of this sort (defined below). */
  private val SetSort: Sort = ctx.mkArraySort(StateSort, BoolSort)

  /** Fresh Z3 constant of sort [[SetSort]] that denotes the abstract set '''S'''.
   * Cf. HHL paper, definition 3. */
  private val S: ArrayExpr[ArraySort[IntSort, IntSort], BoolSort] = ctx.mkConst("S", SetSort).asInstanceOf[ArrayExpr[ArraySort[IntSort, IntSort], BoolSort]]

  /** Environment that maps program variable names and logical variable names to their Z3 integer constants.
   * Populated on the fly when encountering program variables in hyper-assertions. */
  private val progEnv: mutable.Map[String, IntExpr] = mutable.Map.empty[String, IntExpr]

  /** Environment that maps state variable names (introduced by quantifiers) to Z3
   * array constants of sort [[StateSort]]. Populated on the fly when encountering state variables in hyper-assertions. */
  private val stateEnv: mutable.Map[String, ArrayExpr[IntSort, IntSort]] = mutable.Map.empty[String, ArrayExpr[IntSort, IntSort]]

  /**
   * Checks whether the precondition `pre` ''logically entails'' the weakest
   * precondition `wp`. This is done by utilizing the ''Z3 solver'' to check the
   * satisfiability of <code>¬(pre ⇒ wp)</code>.
   *
   * @param pre The user-supplied precondition.
   * @param wp The weakest precondition computed by [[WeakestPrecondition.compute]]
   * @return Z3 [[Status]]:
   *         <ul>
   *          <li>`UNSATISFIABLE` – <code>pre ⊨ wp</code> is valid.</li>
   *          <li>`SATISFIABLE` – implication does <strong>not</strong> hold
   *            (a model serves as counter‑example).</li>
   *          <li>`UNKNOWN` – solver aborted.</li>
   *         </ul>
   */
  def checkEntailment(pre: viper.HHLVerifier.ast.Expr, wp: viper.HHLVerifier.ast.Expr): (Status, Option[Model]) = {
    // encode the precondition and WP
    val z3Pre = encodeBool(WeakestPrecondition.desugarQuantifiers(pre))
    val z3WP = encodeBool(WeakestPrecondition.desugarQuantifiers(wp))
    val z3FinalFormula = ctx.mkNot(ctx.mkImplies(z3Pre, z3WP))

    //println("Z3 encoding Pre: " + z3Pre)
    //println("Z3 encoding WP: " + z3WP)
    //println("Z3 encoding final formula: " + z3FinalFormula)

    // solve ¬(pre ⇒ wp)
    val solver = ctx.mkSolver()
    solver.add(z3FinalFormula)

    val result = solver.check()
    (result, if (result == Status.SATISFIABLE) Some(solver.getModel()) else None)
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
    case LookupExpr(id, index) => encodeBool(resolveLookup(index)(id.asInstanceOf[AssertVar]))
    case StateExistsExpr(AssertVar(name), _) => ctx.mkSelect(S, getStateEnv(name)).asInstanceOf[BoolExpr]
    case _ => sys.error("LogicEncoder: Unexpected expression in boolean conversion: " + expr.toString)
  }

  private def encodeInt(expr: viper.HHLVerifier.ast.Expr): IntExpr = expr match {
    case LookupExpr(AssertVar(stateName), Id(varName)) => ctx.mkSelect(getStateEnv(stateName), getProgEnv(varName)).asInstanceOf[IntExpr]
    case LookupExpr(id, index) => encodeInt(resolveLookup(index)(id.asInstanceOf[AssertVar]))
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

  private def resolveLookup(expr: viper.HHLVerifier.ast.Expr)(implicit assertVar: AssertVar): viper.HHLVerifier.ast.Expr = expr match {
    case Id(_) => LookupExpr(assertVar, expr)
    case Num(_) => expr
    case BoolLit(_) => expr
    case BinaryExpr(e1, op, e2) => BinaryExpr(resolveLookup(e1), op, resolveLookup(e2))
    case UnaryExpr(op, e) => UnaryExpr(op, resolveLookup(e))
    case ImpliesExpr(left, right) => ImpliesExpr(resolveLookup(left), resolveLookup(right))
    case _ => sys.error("LogicEncoder: Unexpected expression in lookup expression: " + expr.toString)
  }

}
