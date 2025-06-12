package viper.HHLVerifier.syntactic

import viper.HHLVerifier.ast._

import scala.::

object Characterizer {

  /** A path of the characterizer representing one path of the (loop-free) program
   *
   * @param pc path condition, a program boolean expression
   * @param subst maps each variable to an expression */
  case class CharPath(pc: Expr, subst: Map[Id, Expr])

  type Characterizer = Seq[CharPath]

  def characterizeLoopFreeProgram(program: HHLProgram): Characterizer = program.methods match {
    case Nil => Nil
    case x :: Nil => characterizeStmt(x.body)
    case _ => sys.error("Characterizer: Cannot yet handle multiple methods") // TODO: Add support
  }

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

  private def applySubstitution(expr: Expr, map: Map[Id, Expr]): Expr = expr match {
    case id@Id(_) => {
      if (!map.contains(id)) expr // in this case there is no more substitution to be done (parameter)
      else applySubstitution(map(id), map)
    }
    case Num(_) | BoolLit(_) => expr
    case BinaryExpr(e1, op, e2) => BinaryExpr(applySubstitution(e1, map), op, applySubstitution(e2, map))
    case UnaryExpr(op, e) => UnaryExpr(op, applySubstitution(e, map))
    case ImpliesExpr(left, right) => ImpliesExpr(applySubstitution(left, map), applySubstitution(right, map))
    case MethodCallExpr(methodName, args) => ??? // TODO: For MultiAssignStmt
    case _ => sys.error("Characterizer: Yet unsupported expression in substitution: " + expr.toString) // TODO: Check which other expressions could be assigned
  }
}