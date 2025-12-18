package viper.HHLVerifier.syntactic.handler

import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.PathBuilder.{CharPath, Characterizer}
import viper.HHLVerifier.syntactic.SyntacticEngine.Triple
import viper.HHLVerifier.syntactic.WeakestPrecondition.substitutePathCondition
import viper.HHLVerifier.syntactic.{SyntacticEngine, WeakestPrecondition}
import viper.HHLVerifier.typing.StateType

object IfElseHandler {

  /**
   * Performs the syntactic handling of a single `if-else` statement of which either
   * the `ifStmt` or the `elseStmt` requires at least one split.
   *
   * Conceptually, this splits the surrounding statement
   * {{{
   *    before ; if (cond) ifStmt else elseStmt ; after
   * }}}
   * into multiple verification triples that can then be recursively divided further
   * (if necessary) and finally be fed into the WP pipeline.
   *
   * The method works as follows:
   *  - It first guards against illegal modifications of the path condition by
   *    checking that the branch condition `cond` does not read variables that
   *    are written in the `if` or `else` bodies.
   *  - It finds the first structural split in each branch (loop, method call,
   *    nested `if-else`, ...) via [[findFirstStructuralSplit]], and delegates
   *    handling of that split to the appropriate handler.
   *  - It reconstructs a (possibly empty) `if-else` "prefix" and "suffix"
   *    from the parts before/after the structural split in each branch, and
   *    merges them into the `before` / `after` triples.
   *  - The precondition of the `if-else` block is just the conjunction of the two
   *    branch preconditions incorporated with the (negated) condition as a premise.
   *  - It combines the branch postconditions into a single hyper
   *    postcondition with [[constructCombinedPostcondition]].
   *
   * @param ifs The `if-else` statement to handle.
   * @param before Surrounding code that executes before `ifs`.
   * @param after Surrounding code that executes after `ifs`.
   * @param pre Incoming preconditions of the whole block.
   * @param post Desired postconditions after the whole block.
   * @param name A human-readable name for this context, used in triple labels.
   * @return A sequence of triples that collectively represent the `if-else`.
   */
  def handle(ifs: IfElseStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple] = ifs match {
    case IfElseStmt(cond, ifStmt, elseStmt) => {
      if (pathConditionModified(ifs)) {
        sys.error("IfElseHandler: Changes to the path condition detected")
      }

      val (thenPrefix, thenTargetOpt, thenSuffix) = findFirstStructuralSplit(ifStmt)
      val (elsePrefix, elseTargetOpt, elseSuffix) = findFirstStructuralSplit(elseStmt)

      val (thenPre, thenPost, thenRemaining) = thenTargetOpt
        .map(findPrePostAndRemainingTriples(_, name))
        .getOrElse(Nil, Nil, Nil)

      val (elsePre, elsePost, elseRemaining) = elseTargetOpt
        .map(findPrePostAndRemainingTriples(_, name))
        .getOrElse(Nil, Nil, Nil)

      val blockPrefix = (thenPrefix, elsePrefix) match {
        case (CompositeStmt(Nil), CompositeStmt(Nil)) => None
        case _ => Some(IfElseStmt(cond, thenPrefix, elsePrefix))
      }

      val blockSuffix = (thenSuffix, elseSuffix) match {
        case (CompositeStmt(Nil), CompositeStmt(Nil)) => None
        case _ => Some(IfElseStmt(cond, thenSuffix, elseSuffix))
      }

      val newBefore = before match {
        case CompositeStmt(xs) => CompositeStmt(xs ++ blockPrefix.toSeq)
      }

      val newAfter = after match {
        case CompositeStmt(xs) => CompositeStmt(blockSuffix.toSeq ++ xs)
      }

      // We use the WP construction to include the branch condition into the precondition, for which we need a characterizer
      //val characterizerThen = Characterizer(Seq(CharPath(cond, Map.empty)))
      //val characterizerElse = Characterizer(Seq(CharPath(UnaryExpr("!", cond), Map.empty)))

      //val blockPre =
      //  List(
      //    Option.when(thenPre != Nil)(WeakestPrecondition.compute(characterizerThen, thenPre, false)),
      //    Option.when(elsePre != Nil)(WeakestPrecondition.compute(characterizerElse, elsePre, false))
      //  ).flatten

      val thenPreGuarded = thenPre.map(p => guardPre(p, cond))
      val elsePreGuarded = elsePre.map(p => guardPre(p, UnaryExpr("!", cond)))

      val blockPre = thenPreGuarded ++ elsePreGuarded

      val blockPost = constructCombinedPostcondition(thenPost, elsePost, ifs)

      val tripleBefore = Triple(
        newBefore,
        pre,
        blockPre,
        name + " > before if-else"
      )

      val tripleAfter = Triple(
        newAfter,
        blockPost,
        post,
        name + " > after if-else"
      )

      List(tripleBefore) ++ thenRemaining ++ elseRemaining ++ List(tripleAfter)
    }
  }

  /**
   * Helper function to find the first structurally interesting statement in a composite statement.
   *
   * @param s Composite statement representing a branch body.
   * @return A triple `(prefix, targetOpt, suffix)` where:
   *         - `prefix` is the split-free code before the first structural split,
   *         - `targetOpt` is the first structural-split statement itself (if any),
   *         - `suffix` is the remaining code after that statement.
   *         If no structural split is found, `targetOpt` is `None` and `suffix`
   *         is empty.
   */
  private def findFirstStructuralSplit(s: CompositeStmt): (CompositeStmt, Option[Stmt], CompositeStmt) = s match {
    case CompositeStmt(stmts) => {
      val (before, targetAndAfter) = stmts.span(!SyntacticEngine.hasStructuralSplit(_))
      targetAndAfter match {
        case Nil => (CompositeStmt(before), None, CompositeStmt(Nil)) // no structural split found in this branch
        case target :: after => (CompositeStmt(before), Some(target), CompositeStmt(after))
      }
    }
  }

  /**
   * Helper function to delegates handling of a statement that requires structural
   * handling and extracts its pre/postconditions and any remaining triples.
   *
   * @param s The structural statement (loop, call, nested if-else, ...)
   * @param name Context name used to label the generated triples.
   * @return `(pre, post, remaining)` where:
   *         - `pre`  is the precondition required before `s`,
   *         - `post` is the postcondition provided after `s`,
   *         - `remaining` are the triples that must be verified according to
   *           the respective handler.
   */
  private def findPrePostAndRemainingTriples(s: Stmt, name: String): (Seq[Expr], Seq[Expr], Seq[Triple]) = s match {
    case ws @ WhileLoopStmt(_, _, _, _, _) => {
      val triples = LoopRuleSelector
        .select(ws)
        .handle(ws, CompositeStmt(Nil), CompositeStmt(Nil), Nil, Nil, name + " > if-else")

      (
        triples.head.post, // based on the invariant of the "LoopRuleHandler" this is the precondition of the loop
        triples.last.pre, // based on the invariant of the "LoopRuleHandler" this is the precondition of the loop
        triples.drop(1).dropRight(1) // we still need to check all loop-specific triples
      )
    }
    case MethodCallStmt(_, _) | MultiAssignStmt(_, _) => {
      val triples = MethodCallHandler
        .handle(s, CompositeStmt(Nil), CompositeStmt(Nil), Nil, Nil, name + " > if-else")

      (
        triples.head.post,
        triples.last.pre,
        Nil
      )
    }
    case ifs @ IfElseStmt(_, _, _) => {
      val triples = IfElseHandler
        .handle(ifs, CompositeStmt(Nil), CompositeStmt(Nil), Nil, Nil, name + " > if-else")

      (
        triples.head.post,
        triples.last.pre,
        triples.drop(1).dropRight(1)
      )
    }
  }

  /**
   * Helper function that checks whether the `if-else` branch condition depends on
   * variables modified inside the `if-else` body.
   */
  private def pathConditionModified(stmt: IfElseStmt): Boolean = {
    stmt match {
      case IfElseStmt(cond, _, _) => {
        varsRead(cond)
          .intersect(varsWritten(stmt))
          .nonEmpty
      }
    }
  }

  /**
   * Collects all identifier occurrences that are read in an expression.
   *
   * Traverses the expression tree and returns the set of [[Id]] nodes that
   * represent variable reads.
   *
   * @param e The expression to analyze.
   * @return The set of identifiers that are read in `e`.
   */
  def varsRead(e: Expr): Set[Id] = e match {
    case id@Id(_) => Set(id)
    case Num(_) | BoolLit(_) | StateExistsExpr(_, _) | AssertVar(_) => Set.empty
    case BinaryExpr(e1, _, e2) => varsRead(e1) ++ varsRead(e2)
    case UnaryExpr(_, e) => varsRead(e)
    case ImpliesExpr(left, right) => varsRead(left) ++ varsRead(right)
    case Assertion(_, _, body) => varsRead(body)
    case LookupExpr(_, index) => varsRead(index)
  }

  /**
   * Collects all identifiers that are written by a statement.
   *
   * Traverses the statement and returns the set of variables that appear on
   * the left-hand side of assignments or multi-assignments.
   *
   * @param s The statement to analyze.
   * @return The set of identifiers whose values may be modified by `s`.
   */
  def varsWritten(s: Stmt): Set[Id] = s match {
    case AssignStmt(left, _) => Set(left)
    case MultiAssignStmt(left, _) => left.toSet
    case IfElseStmt(_, ifStmt, elseStmt) => varsWritten(ifStmt) ++ varsWritten(elseStmt)
    case CompositeStmt(stmts) => stmts.flatMap(varsWritten).toSet
    case WhileLoopStmt(_, body, _, _, _) => varsWritten(body)
    case _ => Set.empty
  }

  /**
   * Combines the branch postconditions of an `if-else` into a single
   * hyper postcondition.
   *
   * The handler currently supports postconditions of the shape
   * {{{
   *    forall <_s1>, ..., <_sn> :: ...
   * }}}
   * in each branch (or one branch being empty). The combination is done
   * using a disjunctive construction over a shared set of assertion variables:
   *
   *  - For two postconditions `thenPost` and `elsePost`, each with their own
   *    universally quantified assertion variables (`n` for `thenPost`, `m`
   *    for `elsePost`), we:
   *      - choose a number `k` of shared assertion variables based on the
   *        pigeonhole principle (`k = n + m - 1`),
   *      - generate all subsets of size `n` and `m` over these variables,
   *      - for each subset, substitute the branch-specific assertion
   *        variables with the chosen subset,
   *      - disjoin all resulting branch formulas.
   *  - The final result is a single `forall` over the `k` shared
   *    assertion variables whose body is this big disjunction.
   *
   * If only one branch has a universal postcondition, that one is returned
   * unchanged. Any other combination shape is currently rejected.
   *
   * @param thenPost Postcondition(s) from the `then` branch.
   * @param elsePost Postcondition(s) from the `else` branch.
   * @param stmt The if-else statement we are reasoning about.
   * @return A single combined postcondition sequence.
   */
  private def constructCombinedPostcondition(thenPost: Seq[Expr], elsePost: Seq[Expr], stmt: IfElseStmt): Seq[Expr] = (thenPost, elsePost) match {
    case (Seq(thenAss @ Assertion("forall", _, _)), Seq(elseAss @ Assertion("forall", _, _))) => {
      val (thenVars, thenCore) = flattenForall(thenAss)
      val (elseVars, elseCore) = flattenForall(elseAss)

      val n = thenVars.length
      val m = elseVars.length
      val k = n + m - 1 // minimum number of k by pigeonhole principle

      val newAssertVars = (1 to k).toList.map(i => AssertVar("_s" + i))

      // generate all combinations for the then post and the else post
      val thenSubsets = generateCombinations(newAssertVars, n)
      val elseSubsets = generateCombinations(newAssertVars, m)

      val thenDisjuncts = thenSubsets.map { curr =>
        val mapping = thenVars.zip(curr).toMap
        val conditions = curr.map(x => substitutePathCondition(stmt.cond, x))
        //ImpliesExpr(
        //  generateBinaryChain(conditions, "&&"),
          substituteAssertVars(thenCore)(mapping)
        //)
      }

      val elseDisjuncts = elseSubsets.map { curr =>
        val mapping = elseVars.zip(curr).toMap
        val conditions = curr.map(x => substitutePathCondition(UnaryExpr("!", stmt.cond), x))
        //ImpliesExpr(
        //  generateBinaryChain(conditions, "&&"),
          substituteAssertVars(elseCore)(mapping)
        //)
      }

      Seq(
        WeakestPrecondition.desugarQuantifiers(
          Assertion(
            "forall",
            newAssertVars.map(x => AssertVarDecl(x, StateType())),
            generateBinaryChain(thenDisjuncts ++ elseDisjuncts, "||")
          )
        )
      )
    }
    case (Seq(thenAss @ Assertion("forall", _, _)), Nil) => Seq(guardForallWithPathCondition(thenAss, stmt.cond))
    case (Nil, Seq(elseAss @ Assertion("forall", _, _))) => Seq(guardForallWithPathCondition(elseAss, UnaryExpr("!", stmt.cond)))
    case _ => sys.error("IfElseHandler: Can only handle \"forall <_s1>, ..., <_si> :: ...\" postconditions in if-else yet.")
  }

  /**
   * Helper function to wrap a universal assertion with a branch path condition.
   */
  private def guardForallWithPathCondition(assertion: Assertion, pathCond: Expr): Expr = {
    val (vars, core) = flattenForall(assertion)
    if (hasNestedAssertion(core)) sys.error(f"IfElseHandler: Illegal assertion found in ${assertion}.")
    val conditions = vars.map(x => substitutePathCondition(pathCond, x))
    val pcChain = generateBinaryChain(conditions, "&&")

    val guardedCore = core match {
      case ImpliesExpr(stateExists, realBody) =>
        // we want to put the pc after the StateExistsExpr
        ImpliesExpr(
          stateExists,
          ImpliesExpr(
            pcChain,
            realBody
          )
        )
      case other => ImpliesExpr(pcChain, other)
    }

    WeakestPrecondition.desugarQuantifiers(
      Assertion(
        "forall",
        vars.map(v => AssertVarDecl(v, StateType())),
        guardedCore
      )
    )
  }

  private def addPathCondition(pc: Expr): Expr = {
    val assertVar = AssertVar("_intState")
    Assertion("forall", List(AssertVarDecl(assertVar, StateType())),
      ImpliesExpr(
        StateExistsExpr(assertVar, false),
        WeakestPrecondition.substitutePathCondition(pc, assertVar)
      )
    )
  }

  /**
   * Helper function to flatten nested `forall` assertions into a list of assertion variables
   * and a quantifier-free core.
   */
  private def flattenForall(expr: Expr): (List[AssertVar], Expr) = expr match {
    case Assertion("forall", decls, body) => {
      val (recResult, core) = flattenForall(body)
      (recResult ++ decls.map(_.vName), core)
    }
    case _ => (Nil, expr)
  }

  /**
   * Helper function that returns true iff there is any nested assertion of the
   * specified type in this expression.
   */
  private def hasNestedAssertion(e: Expr, assertionType: Option[String] = None): Boolean = e match {
    case Assertion(t, _, _) if assertionType.forall(_ == t) => true
    case Assertion(_, _, body) => hasNestedAssertion(body, assertionType)
    case BinaryExpr(e1, _, e2) => hasNestedAssertion(e1, assertionType) || hasNestedAssertion(e2, assertionType)
    case UnaryExpr(_, inner) => hasNestedAssertion(inner, assertionType)
    case ImpliesExpr(left, right) => hasNestedAssertion(left, assertionType) || hasNestedAssertion(right, assertionType)
    case LookupExpr(_, index) => hasNestedAssertion(index, assertionType)
    case Id(_) | Num(_) | BoolLit(_) | StateExistsExpr(_, _) | AssertVar(_) => false
  }


  /**
   * Helper function to generate all combinations (subsets) of size `r` from a list.
   *
   * Used to assign different tuples of shared assertion variables to the
   * branch-specific assertion variable lists when combining postconditions
   * in [[constructCombinedPostcondition]].
   *
   * @param xs Input list of elements.
   * @param r Desired subset size.
   * @tparam A Element type of `xs`.
   * @return All subsets of `xs` of size exactly `r`.
   */
  private def generateCombinations[A](xs: List[A], r: Int): List[List[A]] = {
    if (r <= 0) List(Nil)
    else xs match {
      case Nil => Nil
      case h :: t => generateCombinations(t, r-1).map(h :: _) ::: generateCombinations(t, r)
    }
  }

  /**
   * Helper function to substitute assertion variables in an expression according to a mapping.
   *
   * @note Assertions are not expected here and are rejected.
   */
  private def substituteAssertVars(expr: Expr)(implicit map: Map[AssertVar, AssertVar]): Expr = expr match {
    case Id(_) | Num(_) | BoolLit(_) => expr
    case StateExistsExpr(id: AssertVar, err) => StateExistsExpr(map.getOrElse(id, sys.error("IfElseHandler: Unknown assertVar found " + id)), err)
    case LookupExpr(id: AssertVar, index) => LookupExpr(map.getOrElse(id, sys.error("IfElseHandler: Unknown assertVar found " + id)), substituteAssertVars(index))
    case a: Assertion => sys.error("IfElseHandler: Illegal assertion found: " + a)
    case BinaryExpr(e1, op, e2) => BinaryExpr(substituteAssertVars(e1), op, substituteAssertVars(e2))
    case UnaryExpr(op, e) => UnaryExpr(op, substituteAssertVars(e))
    case ImpliesExpr(left, right) => ImpliesExpr(substituteAssertVars(left), substituteAssertVars(right))
  }

  /**
   * Helper function to build a left-associated chain of binary expressions for a list of expressions.
   */
  private def generateBinaryChain(xs: Seq[Expr], binaryOp: String): Expr = xs match {
    case Nil => binaryOp match {
      case "||" => BoolLit(false)
      case "&&" => BoolLit(true)
      case _ => sys.error("IfElseHandler: Unsupported binary op in chain generation: " + binaryOp)
    }
    case _ => xs.reduceLeft((acc, e) => BinaryExpr(acc, binaryOp, e))
  }

  private def guardPre(e: Expr, pc: Expr): Expr = e match {
    case a @ Assertion("forall", _, _) => guardForallWithPathCondition(a, pc)
    case other =>
      sys.error(s"IfElseHandler: Expected a forall-precondition, got: $other")
  }
}
