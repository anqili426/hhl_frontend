package viper.HHLVerifier.syntactic

import viper.HHLVerifier.ast._

object PathBuilder {

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
   * A `Characterizer` is an element consisting of:
   *    - A list of [[CharPath]] objects, each element representing all paths of a program. The characterizer
   *    itself covers exactly all paths of the program.
   *    - A set of [[HavocVar]] objects introduced by `havoc` statements along all explored paths. They are tracked
   *    globally and are required later when computing the weakest precondition, as they require special treatement.
   */
  case class Characterizer(
    paths: Seq[CharPath],
    havocs: Set[HavocVar],
    asserts: Map[Stmt, Seq[CharPath]]
  ) {
    def ++(that: Characterizer): Characterizer =
      Characterizer(paths ++ that.paths, havocs ++ that.havocs, asserts ++ that.asserts)

    def mapPaths(f: CharPath => CharPath): Characterizer =
      copy(paths = paths.map(f))

    def withHavoc(newVar: HavocVar): Characterizer =
      copy(havocs = havocs + newVar)

    def withAssert(assert: Stmt, paths: Seq[CharPath]): Characterizer = {
      copy(asserts = asserts + (assert -> paths))
    }
  }

  object Characterizer {
    val empty: Characterizer = Characterizer(Seq(CharPath(BoolLit(true), Map.empty)), Set.empty, Map.empty)
  }

  var genSymCounter: Int = 0

  /**
   * Generates a unique symbol by appending a counter to a given string. Each time the function is called,
   * [[genSymCounter]] increments to ensure that the resulting symbol is unique.
   *
   * @param s The base string to which a unique suffix will be added.
   * @return A new string formed by concatenating the input string with an underscore (`_`) and a counter value.
   */
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
    case Nil => Characterizer.empty
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
  def characterizeStmt(stmt: Stmt, acc: Characterizer = Characterizer.empty): Characterizer = stmt match {
    case CompositeStmt(Nil) => acc
    case CompositeStmt(x :: xs) => {
      val firstRes = characterizeStmt(x, acc)
      characterizeStmt(CompositeStmt(xs), firstRes)
    }
    case AssignStmt(left, right) => acc.mapPaths {
      case CharPath(pc, subst) => CharPath(pc, subst + (left -> applySubstitution(right, subst)))
    }
    case MultiAssignStmt(left, right) => ??? // TODO
    case IfElseStmt(cond, ifStmt, elseStmt) => {
      // Fold over all incoming paths and accumulate both paths and havoc-vars
      acc.paths.foldLeft(Characterizer(Seq.empty, acc.havocs, acc.asserts)) {
        case (accum, in@CharPath(pcBefore, substBefore)) =>
          val c = applySubstitution(cond, substBefore)

          // Run each branch starting from this single incoming path.
          val ifResRaw   = characterizeStmt(ifStmt, Characterizer(Seq(in), accum.havocs, accum.asserts))
          val elseResRaw = characterizeStmt(elseStmt, Characterizer(Seq(in), accum.havocs, accum.asserts))

          // Add the current branch condition to the path condition
          val ifRes = ifResRaw.mapPaths(out =>
            CharPath(BinaryExpr(c, "&&", out.pc), out.subst)
          )
          val elseRes = elseResRaw.mapPaths(out =>
            CharPath(BinaryExpr(UnaryExpr("!", c), "&&", out.pc), out.subst)
          )

          accum ++ ifRes ++ elseRes
      }
    }
    case AssumeStmt(e) => acc.mapPaths {
      case CharPath(pc, subst) => CharPath(BinaryExpr(applySubstitution(e, subst), "&&", pc), subst)
    }
    case HyperAssumeStmt(e) => acc.mapPaths {
      case CharPath(pc, subst) => CharPath(BinaryExpr(applySubstitution(e, subst), "&&", pc), subst)
    }
    case AssertStmt(e) => acc.mapPaths {
      case CharPath(pc, subst) => CharPath(BinaryExpr(applySubstitution(e, subst), "&&", pc), subst)
    }
      .withAssert(stmt, acc.paths)
    case HyperAssertStmt(e) => acc.mapPaths {
      // TODO: Think about correct handling ==> splitting up program (similar to loops and function calls)
      case CharPath(pc, subst) => CharPath(BinaryExpr(applySubstitution(e, subst), "&&", pc), subst)
    }
    case HavocStmt(stmt:Id, _) => {
      val newVar = HavocVar(genSym("*havoc"))
      acc.mapPaths {
        case CharPath(pc, subst) => CharPath(pc, subst + (stmt -> newVar))
      }
        .withHavoc(newVar)
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