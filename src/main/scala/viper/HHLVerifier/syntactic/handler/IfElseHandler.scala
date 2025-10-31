package viper.HHLVerifier.syntactic.handler

import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.PathBuilder.{CharPath, Characterizer}
import viper.HHLVerifier.syntactic.SyntacticEngine.Triple
import viper.HHLVerifier.syntactic.{SyntacticEngine, WeakestPrecondition}
import viper.HHLVerifier.typing.StateType

object IfElseHandler {
  def handle(ifs: IfElseStmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple] = ifs match {
    case IfElseStmt(cond, ifStmt, elseStmt) => {
      if (pathConditionModified(ifs)) {
        sys.error("IfElseHandler: Changes to the path condition detected")
      }

      val (thenPrefix, thenTargetOpt, thenSuffix) = findFirstStructuralSplit(ifStmt)
      val (elsePrefix, elseTargetOpt, elseSuffix) = findFirstStructuralSplit(elseStmt)

      val (thenPre, thenPost, thenRemaining) = thenTargetOpt
        .map(findPrePostAndRemainingTriples(_, name))
        .getOrElse(Nil, Nil, Nil) // TODO: double-check these default values ==> depends on blockPre below

      val (elsePre, elsePost, elseRemaining) = elseTargetOpt
        .map(findPrePostAndRemainingTriples(_, name))
        .getOrElse(Nil, Nil, Nil) // TODO: double-check these default values ==> depends on blockPost below

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
      val characterizerThen = Characterizer(Seq(CharPath(cond, Map.empty)))
      val characterizerElse = Characterizer(Seq(CharPath(UnaryExpr("!", cond), Map.empty)))

      val blockPre =
        List(
          Option.when(thenPre != Nil)(WeakestPrecondition.compute(characterizerThen, thenPre, false)),
          Option.when(elsePre != Nil)(WeakestPrecondition.compute(characterizerElse, elsePre, false))
        ).flatten

      // TODO: This needs to be generalized: How can we do it for arbitrary postconditions? Right now only forall quantified...
      val blockPost = constructCombinedPostcondition(thenPost, elsePost)

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

  private def findFirstStructuralSplit(s: CompositeStmt): (CompositeStmt, Option[Stmt], CompositeStmt) = s match {
    case CompositeStmt(stmts) => {
      val (before, targetAndAfter) = stmts.span(!SyntacticEngine.hasStructuralSplit(_))
      targetAndAfter match {
        case Nil => (CompositeStmt(before), None, CompositeStmt(Nil)) // no structural split found in this branch
        case target :: after => (CompositeStmt(before), Some(target), CompositeStmt(after))
      }
    }
  }

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
        triples // TODO: double-check
      )
    }
  }

  private def pathConditionModified(stmt: IfElseStmt): Boolean = {
    def varsRead(e: Expr): Set[Id] = e match {
      case id@Id(_) => Set(id)
      case Num(_) | BoolLit(_) => Set.empty
      case BinaryExpr(e1, _, e2) => varsRead(e1) ++ varsRead(e2)
      case UnaryExpr(_, e) => varsRead(e)
      case ImpliesExpr(left, right) => varsRead(left) ++ varsRead(right)
    }
    def varsWritten(s: Stmt): Set[Id] = s match {
      case AssignStmt(left, _) => Set(left)
      case MultiAssignStmt(left, _) => left.toSet
      case IfElseStmt(_, ifStmt, elseStmt) => varsWritten(ifStmt) ++ varsWritten(elseStmt)
      case CompositeStmt(stmts) => stmts.flatMap(varsWritten).toSet
      case _ => Set.empty
    }

    stmt match {
      case IfElseStmt(cond, _, _) => {
        varsRead(cond)
          .intersect(varsWritten(stmt))
          .nonEmpty
      }
    }
  }

  private def constructCombinedPostcondition(thenPost: Seq[Expr], elsePost: Seq[Expr]):  Seq[Expr] = (thenPost, elsePost) match {
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
        substituteAssertVars(thenCore)(mapping)
      }

      val elseDisjuncts = elseSubsets.map { curr =>
        val mapping = elseVars.zip(curr).toMap
        substituteAssertVars(elseCore)(mapping)
      }

      Seq(
        WeakestPrecondition.desugarQuantifiers(
          Assertion(
            "forall",
            newAssertVars.map(x => AssertVarDecl(x, StateType())),
            generateOrChain(thenDisjuncts ++ elseDisjuncts)
          )
        )
      )
    }
    case (Seq(Assertion("forall", _, _)), Nil) => thenPost
    case (Nil, Seq(Assertion("forall", _, _))) => elsePost
    case _ => sys.error("IfElseHandler: Can only handle \"forall <_s1>, ..., <_si> :: ...\" postconditions in if-else yet.")
  }

  private def flattenForall(expr: Expr): (List[AssertVar], Expr) = expr match {
    case Assertion("forall", decls, body) => {
      val (recResult, core) = flattenForall(body)
      (recResult ++ decls.map(_.vName), core)
    }
    case _ => (Nil, expr)
  }

  private def generateCombinations[A](xs: List[A], r: Int): List[List[A]] = {
    if (r <= 0) List(Nil)
    else xs match {
      case Nil => Nil
      case h :: t => generateCombinations(t, r-1).map(h :: _) ::: generateCombinations(t, r)
    }
  }

  private def substituteAssertVars(expr: Expr)(implicit map: Map[AssertVar, AssertVar]): Expr = expr match {
    case Id(_) | Num(_) | BoolLit(_) => expr
    case StateExistsExpr(id: AssertVar, err) => StateExistsExpr(map.getOrElse(id, sys.error("IfElseHandler: Unknown assertVar found " + id)), err)
    case LookupExpr(id: AssertVar, index) => LookupExpr(map.getOrElse(id, sys.error("IfElseHandler: Unknown assertVar found " + id)), substituteAssertVars(index))
    case a: Assertion => sys.error("IfElseHandler: Unallowed assertion found: " + a)
    case BinaryExpr(e1, op, e2) => BinaryExpr(substituteAssertVars(e1), op, substituteAssertVars(e2))
    case UnaryExpr(op, e) => UnaryExpr(op, substituteAssertVars(e))
    case ImpliesExpr(left, right) => ImpliesExpr(substituteAssertVars(left), substituteAssertVars(right))
  }

  private def generateOrChain(xs: List[Expr]): Expr = xs match {
    case Nil => BoolLit(false)
    case _ => xs.reduceLeft((acc, e) => BinaryExpr(acc, "||", e))
  }
}
