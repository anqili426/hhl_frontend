package viper.HHLVerifier.syntactic

import viper.HHLVerifier.ast._

object Characterizer {

  /**
   * A path of the characterizer representing one path of a (loop-free) program
   *
   * @param pc    path condition, a program boolean expression, which holds on an initial state if and only if
   *              this initial state can take this path.
   * @param subst maps each variable `x` of the program to an expression `p`, meaning that the variable `x` in
   *              the final state will have the value of the expression `p` in the initial state.
   */
  case class CharPath(pc: Expr, subst: Map[Id, Expr])

  /**
   * A `Characterizer` is a pair consisting of:
   *    - A list of [[CharPath]] objects, each element representing all paths of a program. The characterizer
   *    itself covers exactly all paths of the program.
   *    - A set of [[HavocVar]] objects introduced by `havoc` statements along all explored paths. They are tracked
   *    globally and are required later when computing the weakest precondition, as they require special treatement.
   */
  type Characterizer = (Seq[CharPath], Set[HavocVar])

  var genSymCounter: Int = 0

  private def genSym(s: String): String = {
    genSymCounter += 1
    s + "_" + genSymCounter
  }

  /**
   * Derives a [[Characterizer]] for a '''loop-free''' [[HHLProgram]].
   *
   * @param program a loop-free [[HHLProgram]] to analyze
   * @return        a characterizer capturing all paths of a program. A characterizer is defined as
   *                a list of [[CharPath]]s, where each element of the list covers one path of the program.
   *                The characterizer itself then covers exactly all paths of the program.
   * @throws java.lang.RuntimeException if the program contains more than one
   *                                    method (feature not yet implemented)
   */
  def characterizeLoopFreeProgram(program: HHLProgram): Characterizer = program.methods match {
    case Nil => (Nil, Set.empty)
    case x :: Nil => characterizeStmt(x.body)
    case _ => sys.error("Characterizer: Cannot yet handle multiple methods") // TODO: Add support
  }

  /**
   * Derives a [[Characterizer]] for a '''loop-free''' [[Stmt]]. Recursively
   * '''symbolically characterizes''' a single statement, yielding all feasible execution paths as [[CharPath]] objects.
   *
   * @param stmt a loop-free [[Stmt]] to analyze
   * @return        a characterizer capturing all paths of the statement. A characterizer is defined as
   *                a list of [[CharPath]]s, where each element of the list covers one path of the program.
   *                The characterizer itself then covers exactly all paths of the program.
   */
  def characterizeStmt(stmt: Stmt, acc: Characterizer = (Seq(CharPath(BoolLit(true), Map.empty)), Set.empty)): Characterizer = stmt match {
    case CompositeStmt(Nil) => acc
    case CompositeStmt(x :: xs) => {
      val firstRes = characterizeStmt(x, acc)
      characterizeStmt(CompositeStmt(xs), firstRes)
    }
    case AssignStmt(left, right) => (acc._1.map {
      case CharPath(pc, subst) => CharPath(pc, subst + (left -> applySubstitution(right, subst)))
    }, acc._2)
    case MultiAssignStmt(left, right) => ??? // TODO
    case IfElseStmt(cond, ifStmt, elseStmt) => {
      // Fold over all incoming paths and accumulate both paths and havoc-vars
      acc._1.foldLeft[(Seq[CharPath], Set[HavocVar])]((Seq.empty, acc._2)) {
        case ((pathsAcc, havocAcc), in@CharPath(pcBefore, substBefore)) =>
          val c = applySubstitution(cond, substBefore)

          // Run each branch starting from this single incoming path.
          val (ifPathsRaw, ifHavoc)   = characterizeStmt(ifStmt, (Seq(in), havocAcc))
          val (elsePathsRaw, elseHavoc) = characterizeStmt(elseStmt, (Seq(in), havocAcc))

          // Add the current branch condition to the path condition
          val ifPaths = ifPathsRaw.map(out =>
            CharPath(BinaryExpr(c, "&&", out.pc), out.subst)
          )
          val elsePaths = elsePathsRaw.map(out =>
            CharPath(BinaryExpr(UnaryExpr("!", c), "&&", out.pc), out.subst)
          )

          (pathsAcc ++ ifPaths ++ elsePaths, havocAcc ++ ifHavoc ++ elseHavoc)
      }
    }
    case AssumeStmt(e) => (acc._1.map {
      case CharPath(pc, subst) => CharPath(BinaryExpr(applySubstitution(e, subst), "&&", pc), subst)
    }, acc._2)
    case HyperAssumeStmt(e) => (acc._1.map {
      case CharPath(pc, subst) => CharPath(BinaryExpr(applySubstitution(e, subst), "&&", pc), subst)
    }, acc._2)
    case HavocStmt(stmt:Id, _) => {
      val newVar = HavocVar(genSym("*havoc"))
      (acc._1.map {
        case CharPath(pc, subst) => CharPath(pc, subst + (stmt -> newVar))
      }, acc._2 + newVar)
    }
    case WhileLoopStmt(_, _, _, _, _) => sys.error("Characterizer: Expected a loop-free program")
    case _ => acc
  }

  /**
   * Performs a '''recursive substitution''' of identifiers according to the given mapping.
   *
   * @param expr the expression in which the substitution takes place
   * @param map  a mapping from identifiers to the expressions that replace them
   * @return     a copy of `expr` where every identifier occuring in `map` has been substituted
   */
  def applySubstitution(expr: Expr, map: Map[Id, Expr]): Expr = expr match {
    case id@Id(_) => map.getOrElse(id, expr)
    case Num(_) | BoolLit(_) | StateExistsExpr(_, _) => expr
    case LookupExpr(id, index) => LookupExpr(id, applySubstitution(index, map))
    case Assertion(quantifier, assertVarDecls, body) => Assertion(quantifier, assertVarDecls, applySubstitution(body, map))
    case BinaryExpr(e1, op, e2) => BinaryExpr(applySubstitution(e1, map), op, applySubstitution(e2, map))
    case UnaryExpr(op, e) => UnaryExpr(op, applySubstitution(e, map))
    case ImpliesExpr(left, right) => ImpliesExpr(applySubstitution(left, map), applySubstitution(right, map))
    case MethodCallExpr(methodName, args) => ??? // TODO: For MultiAssignStmt
    case _ => sys.error("Characterizer: Yet unsupported expression in substitution: " + expr.toString) // TODO: Check which other expressions could be assigned
  }
}