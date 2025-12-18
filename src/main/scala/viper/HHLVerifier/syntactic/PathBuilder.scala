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
   * A `Characterizer` compactly represents the (symbolic) behaviors of a program fragment. It can be computed
   * for a statement using the function [[characterizeStmt]] and consists of the following parts:
   *    - A list of [[CharPath]] objects, each representing a single path of a program. A program path is characterized with its
   *    path condition and a variable substitution. The characterizer itself covers exactly all paths of the program.
   *    - A set of [[HavocVar]] objects introduced by `havoc` statements along all explored paths. They are tracked
   *    globally for all paths and are required later when computing the weakest precondition, as they require special treatment.
   *    - A map from assertion statements to the [[CharPath]] objects present at the time of their occurrence. This is later used
   *    to compute the WP for error states, as we need to know the substitution and path condition at the time of the error.
   */
  case class Characterizer(
    paths: Seq[CharPath],
    havocs: Set[HavocVar],
    asserts: Map[Stmt, Seq[CharPath]]
  ) {
    /**
     * Combine two characterizers.
     *  - Concatenates `paths` from both operands.
     *  - Unions `havocs`.
     *  - Merges `asserts` by key and deduplicates per-assert paths based on
     *   `CharPath` equality.
     *
     * @return a characterizer containing the union of information from `this` and `that`.
     */
    def ++(that: Characterizer): Characterizer = {
      val mergedAsserts = (this.asserts.toSeq ++ that.asserts.toSeq)
        .groupMapReduce(_._1)(_._2)(_ ++ _)
        .view
        .mapValues(_.distinctBy(p => (p.pc, p.subst)))
        .toMap

      Characterizer(this.paths ++ that.paths, this.havocs ++ that.havocs, mergedAsserts)
    }

    /**
     * Apply a transformation to every path in `paths`.
     *
     * @param f the path transformation function
     * @return a new characterizer with transformed top-level `paths`.
     */
    def mapPaths(f: CharPath => CharPath): Characterizer =
      copy(paths = paths.map(f))

    /**
     * Add a freshly-introduced havoc variable to the global set.
     *
     * @param newVar the havoc variable to track
     * @return a new characterizer with `newVar` included in `havocs`.
     */
    def withHavoc(newVar: HavocVar): Characterizer =
      copy(havocs = havocs + newVar)

    /**
     * Add an assertion statement and a snapchat of the currently active paths to the characterizer.
     * If an equivalent `assert` statement has already been seen, the new paths are appended in the map.
     *
     * @param assert the assertion statement, ideally an [[AssertStmt]]
     * @param paths the paths active at the time the assertion is encountered.
     * @return a new characterizer with the updated `asserts` mapping.
     */
    def withAssert(assert: Stmt, paths: Seq[CharPath]): Characterizer = {
      val merged = asserts.getOrElse(assert, Seq.empty) ++ paths
      copy(asserts = asserts + (assert -> merged))
    }
  }

  object Characterizer {
    /**
     * Convenience constructor: only `paths`; `havocs` and `asserts` are empty.
     */
    def apply(paths: Seq[CharPath]): Characterizer =
      new Characterizer(paths, Set.empty, Map.empty)

    /**
     * The identity characterizer
     */
    val empty: Characterizer = Characterizer(Seq(CharPath(BoolLit(true), Map.empty)), Set.empty, Map.empty)
  }

  private var genSymCounter: Int = 0

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
   * Derives a [[Characterizer]] for a '''split-free''' [[Stmt]]. Recursively
   * '''symbolically characterizes''' a single statement, yielding all feasible execution paths as [[CharPath]] objects.
   *
   * @param stmt a split-free [[Stmt]] to analyze
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
    case IfElseStmt(cond, ifStmt, elseStmt) => {
      // Fold over all incoming paths and accumulate both paths and havoc-vars
      acc.paths.foldLeft(Characterizer(Seq.empty, acc.havocs, acc.asserts)) {
        case (accum, CharPath(pcBefore, substBefore)) =>
          val c = applySubstitution(cond, substBefore)

          // Add path condition before going into recursion
          val inIf = CharPath(BinaryExpr(c, "&&", pcBefore), substBefore)
          val inElse = CharPath(BinaryExpr(UnaryExpr("!", c), "&&", pcBefore), substBefore)

          // Run each branch starting from this single incoming path.
          val ifRes = characterizeStmt(ifStmt, Characterizer(Seq(inIf), accum.havocs, accum.asserts))
          val elseRes = characterizeStmt(elseStmt, Characterizer(Seq(inElse), accum.havocs, accum.asserts))

          accum ++ ifRes ++ elseRes
      }
    }
    case AssumeStmt(e) => acc.mapPaths {
      case CharPath(pc, subst) => CharPath(BinaryExpr(applySubstitution(e, subst), "&&", pc), subst)
    }
    case AssertStmt(e) => acc.mapPaths {
      case CharPath(pc, subst) => CharPath(BinaryExpr(applySubstitution(e, subst), "&&", pc), subst)
    }
      .withAssert(stmt, acc.paths)
    case HavocStmt(stmt:Id, _) => {
      val newVar = HavocVar(genSym("*havoc"))
      acc.mapPaths {
        case CharPath(pc, subst) => CharPath(pc, subst + (stmt -> newVar))
      }
        .withHavoc(newVar)
    }
    case _: WhileLoopStmt | _: MethodCallStmt | _: MultiAssignStmt | _: HyperAssumeStmt | _: HyperAssertStmt => sys.error("PathBuilder: Expected a split-free program")
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
    case _ => sys.error("PathBuilder: Yet unsupported expression in substitution: " + expr.toString)
  }
}