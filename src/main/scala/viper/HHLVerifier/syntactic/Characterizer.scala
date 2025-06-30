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

  type Characterizer = Seq[CharPath]

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
    case Nil => Nil
    case x :: Nil => characterizeStmt(x.body)
    case _ => sys.error("Characterizer: Cannot yet handle multiple methods") // TODO: Add support
  }

  /**
   * Recursively '''symbolically characterizes''' a single statement, yielding all feasible execution
   * paths as [[CharPath]] objects.
   */
  private def characterizeStmt(stmt: Stmt, acc: Seq[CharPath] = Seq(CharPath(BoolLit(true), Map.empty))): Characterizer = stmt match {
    case CompositeStmt(Nil) => acc
    case CompositeStmt(x :: xs) => {
      val firstRes = characterizeStmt(x, acc)
      characterizeStmt(CompositeStmt(xs), firstRes)
    }
    case AssignStmt(left, right) => acc.map {
      case CharPath(pc, subst) => CharPath(pc, subst + (left -> applySubstitution(right, subst)))
    }
    case MultiAssignStmt(left, right) => ??? // TODO
    case IfElseStmt(cond, ifStmt, elseStmt) => {
      // we need to apply the substitution to the condition as well, but in the initial state of the if-statement
      val ifRes = for {
        CharPath(pcBefore, substBefore) <- acc
        CharPath(pcAfter, substAfter) <- characterizeStmt(ifStmt, acc)
      } yield CharPath(BinaryExpr(applySubstitution(cond, substBefore), "&&", pcAfter), substAfter)
      val elseRes = for {
        CharPath(pcBefore, substBefore) <- acc
        CharPath(pcAfter, substAfter) <- characterizeStmt(elseStmt, acc)
      } yield CharPath(BinaryExpr(UnaryExpr("!", applySubstitution(cond, substBefore)), "&&", pcAfter), substAfter)
      ifRes ++ elseRes
    }
    case HavocStmt(_, _) => sys.error("Characterizer: Cannot yet handle havoc: " + stmt.toString)
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
    case Num(_) | BoolLit(_) => expr
    case BinaryExpr(e1, op, e2) => BinaryExpr(applySubstitution(e1, map), op, applySubstitution(e2, map))
    case UnaryExpr(op, e) => UnaryExpr(op, applySubstitution(e, map))
    case ImpliesExpr(left, right) => ImpliesExpr(applySubstitution(left, map), applySubstitution(right, map))
    case MethodCallExpr(methodName, args) => ??? // TODO: For MultiAssignStmt
    case _ => sys.error("Characterizer: Yet unsupported expression in substitution: " + expr.toString) // TODO: Check which other expressions could be assigned
  }
}