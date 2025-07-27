package viper.HHLVerifier.syntactic

import com.microsoft.z3._
import viper.HHLVerifier.ast._
import Characterizer._
import viper.HHLVerifier.syntactic.WeakestPrecondition.substitutePathCondition

object SyntacticEngine {

  var verificationResult: Int = 0

  private case class Triple(stmt: Stmt, pre: Seq[viper.HHLVerifier.ast.Expr], post: Seq[viper.HHLVerifier.ast.Expr], name: String = "")

  def verify(program: HHLProgram): Int = {
    program.methods.foreach { method =>
      println("----------")
      println("Method \"" + method.mName + "\"")

      val split = loopSplit(Triple(method.body, method.pre, method.post, "top-level"))
      //println(split)

      // Verifying all triples
      split
        .foreach { triple => verifyLoopFreeTriple(triple, getAllProgVars(method)) }

      // verifyLoopFreeTriple(Triple(method.body, method.pre, method.post), method.params, "top-level")(method) // old version for loop-free programs
    }
    verificationResult
  }

  private def verifyLoopFreeTriple(triple: Triple, progVars: Seq[Id]): Boolean = triple match {
    case Triple(body, pre, post, name) => {
      if (pre.isEmpty || post.isEmpty) {
        println(f"\t Error ($name): Pre and/or postcondition is empty.")
        verificationResult = 2
        false
      } else {
        val characterizer: Characterizer = Characterizer.characterizeStmt(body)
        //println(characterizer)
        val weakestPrecondition: viper.HHLVerifier.ast.Expr = WeakestPrecondition.compute(characterizer, post)
        //println(weakestPrecondition)
        val combinedPrecondition: viper.HHLVerifier.ast.Expr = pre.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x))

        // Z3 encoding
        val encoder: LogicEncoderNew = new LogicEncoderNew
        val result = encoder.checkImplication(combinedPrecondition, weakestPrecondition, progVars)

        result._1 match {
          case Status.UNSATISFIABLE =>
            println(f"\tValid ($name): Precondition implies WP.")
            if (verificationResult != 2) verificationResult = 1
            true
          case Status.SATISFIABLE =>
            println(f"\tInvalid ($name): Counterexample found.")
            verificationResult = 2
            false
          case Status.UNKNOWN =>
            println(f"\tUnknown ($name): Z3 couldn't determine the result.")
            verificationResult = 2 // for now, we handle "unknown" as invalid
            false
        }
      }
    }
  }

  private def loopSplit(triple: Triple): Seq[Triple] = triple match {
    case Triple(stmt, pre, post, name) => {
      stmt match {
        case CompositeStmt(stmts) => {
          val (before, loopAndAfter) = stmts.span {
            case _: WhileLoopStmt => false
            case _ => true
          }
          loopAndAfter match {
            case WhileLoopStmt(cond, body, inv, decr, rule) :: after => {
              val mappedInvariant = inv.map(_._2)
              val loopPostcondition = handleRuleForallExists(WhileLoopStmt(cond, body, inv, decr, rule))
              val prefixOpt = Some(Triple(CompositeStmt(before), pre, inv.map(_._2), name + " > [P] prefix [I]"))
              val bodyOpt = Some(Triple(IfElseStmt(cond, body, CompositeStmt(Nil)), mappedInvariant, mappedInvariant, name + " > [I] if (b) {C} [I]"))
              val suffixOpt = Some(Triple(CompositeStmt(after), List(loopPostcondition), post, name + " > [Q_loop] suffix [Q]"))
              List(prefixOpt, bodyOpt, suffixOpt).flatten
            }
            case _ => List(triple) // no loop found in stmt
          }
        }
        case IfElseStmt(_, ifStmt, elseStmt) => ???
        case WhileLoopStmt(_, body, _, _, _) => ???
        case _ => ???
      }
    }
  }

  private def handleRuleForallExists(stmt: WhileLoopStmt): viper.HHLVerifier.ast.Expr = stmt match {
    case WhileLoopStmt(cond, body, inv, decr, rule) => {
      val mappedInvariant = inv.map(_._2)
      substitutionForallExists(mappedInvariant.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x)))(cond)
    }
  }

  private def substitutionForallExists(inv: viper.HHLVerifier.ast.Expr, noForallAfterExists: Boolean = true)(implicit loopCondition: viper.HHLVerifier.ast.Expr): viper.HHLVerifier.ast.Expr = inv match {
    case Assertion("exists", List(AssertVarDecl(vName, vType)), body) => Assertion("exists", List(AssertVarDecl(vName, vType)), BinaryExpr(substitutionForallExists(body, false), "&&", ImpliesExpr(UnaryExpr("!", substitutePathCondition(loopCondition, vName)), StateExistsExpr(vName, false)))) // cf. Hypra paper, p. 19, bottom
    case Assertion("exists", _, _) => sys.error("SyntacticEngine: Tried to apply \"forallExistsRule\", but found non-desugared quantifier.")
    case Assertion("forall", assertVarDecls, body) =>
      if (!noForallAfterExists) sys.error("SyntacticEngine: Tried to apply \"forallExistsRule\", but invariant \"no forall after exists quantifier\" was violated.")
      else Assertion("forall", assertVarDecls, substitutionForallExists(body, noForallAfterExists))
    case BinaryExpr(e1, op, e2) => BinaryExpr(substitutionForallExists(e1, noForallAfterExists), op, substitutionForallExists(e2, noForallAfterExists))
    case UnaryExpr(op, e) => UnaryExpr(op, substitutionForallExists(e, noForallAfterExists))
    case ImpliesExpr(left, right) => ImpliesExpr(substitutionForallExists(left, noForallAfterExists), substitutionForallExists(right, noForallAfterExists))
    case _ => inv // TODO: Double-check which other Expr are possible
  }

  private def getAllProgVars(method: Method): Seq[Id] = {
    method.params ++ method.res ++ getAllProgVarsHelper(method.body).toSeq
  }

  private def getAllProgVarsHelper(stmt: Stmt): Set[Id] = stmt match {
    case CompositeStmt(x :: xs) => getAllProgVarsHelper(x) ++ getAllProgVarsHelper(CompositeStmt(xs))
    case IfElseStmt(_, ifStmt, elseStmt) => getAllProgVarsHelper(ifStmt) ++ getAllProgVarsHelper(elseStmt)
    case WhileLoopStmt(_, body, _, _, _) => getAllProgVarsHelper(body)
    case PVarDecl(vName, _) => Set(vName)
    case _ => Set.empty[Id]
  }
}

