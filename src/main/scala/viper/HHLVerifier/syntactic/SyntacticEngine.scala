package viper.HHLVerifier.syntactic

import com.microsoft.z3._
import viper.HHLVerifier.ast._
import Characterizer._

object SyntacticEngine {

  var verificationResult: Int = 0

  case class Triple(stmt: Stmt, pre: Seq[viper.HHLVerifier.ast.Expr], post: Seq[viper.HHLVerifier.ast.Expr], name: String = "")

  def verify(program: HHLProgram): Int = {
    verificationResult = 0

    program.methods.foreach { method =>
      println("----------")
      println("Method \"" + method.mName + "\"")

      val progVars = getAllProgVars(method)
      val split = loopSplit(Triple(method.body, method.pre, method.post, "top-level"), progVars)
      //println(split)

      // Verifying all triples
      split
        .foreach { triple => verifyLoopFreeTriple(triple, progVars) }

      // verifyLoopFreeTriple(Triple(method.body, method.pre, method.post), method.params, "top-level")(method) // old version for loop-free programs
    }
    verificationResult
  }

  private def verifyLoopFreeTriple(triple: Triple, progVars: Seq[Id]): Boolean = triple match {
    case Triple(body, pre, post, name) => {
      if (pre.isEmpty || post.isEmpty) {
        println(f"\tError ($name): Pre and/or postcondition is empty.")
        verificationResult = 1
        false
      } else {
        val characterizer: Characterizer = Characterizer.characterizeStmt(body)
        //println(characterizer)
        val weakestPrecondition: viper.HHLVerifier.ast.Expr = WeakestPrecondition.compute(characterizer, post)
        //println(weakestPrecondition)
        val combinedPrecondition: viper.HHLVerifier.ast.Expr = pre.reduceLeft((acc, x) => BinaryExpr(acc, "&&", x))

        // Z3 encoding
        val encoder: LogicEncoderNew = new LogicEncoderNew
        val result = encoder.checkEntailment(combinedPrecondition, weakestPrecondition, progVars)

        result._1 match {
          case Status.UNSATISFIABLE =>
            println(f"\tValid ($name): Precondition implies WP.")
            if (verificationResult != 1) verificationResult = 2
            true
          case Status.SATISFIABLE =>
            println(f"\tInvalid ($name): Counterexample found.")
            verificationResult = 1
            false
          case Status.UNKNOWN =>
            println(f"\tUnknown ($name): Z3 couldn't determine the result.")
            verificationResult = 1 // for now, we handle "unknown" as invalid
            false
        }
      }
    }
  }

  private def loopSplit(triple: Triple, progVars: Seq[Id]): Seq[Triple] = triple match {
    case Triple(stmt, pre, post, name) => {
      stmt match {
        case CompositeStmt(stmts) => {
          val (before, loopAndAfter) = stmts.span {
            case _: WhileLoopStmt => false
            case _ => true
          }
          loopAndAfter match {
            case (ws@WhileLoopStmt(_, _, _, _, _)) :: after => {
              val ruleHandler = RuleSelector.select(ws, progVars)
              ruleHandler.handle(ws, CompositeStmt(before), CompositeStmt(after), pre, post, progVars, name)
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

