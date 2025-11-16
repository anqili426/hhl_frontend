package viper.HHLVerifier.syntactic.handler

import viper.HHLVerifier.ast._
import viper.HHLVerifier.syntactic.PathBuilder
import viper.HHLVerifier.syntactic.SyntacticEngine.Triple

object MethodCallHandler {
  /**
   * Handles a single method call ([[MultiAssignStmt]] or [[MethodCallStmt]]) in
   * the program.
   *
   * Conceptually splits
   * {{{
   *    before ; call ; after
   * }}}
   * into two separate triples, before and after the call:
   *
   *  - the "before-call" triple:
   *    - statement: `before`
   *    - precondition: `pre`
   *    - postcondition: called method's precondition, with formal parameters
   *      substituted by the actual arguments,
   *
   *  - the "after-call" triple:
   *    - statement: `after`
   *    - precondition: called method's postcondition, with both parameters
   *      and result variables substituted by actual arguments and result
   *      variables,
   *    - postcondition: `post`.
   *
   * @param call The method call statement (or multi-assignment with call).
   * @param before Code executing before the call.
   * @param after Code executing after the call.
   * @param pre Incoming preconditions for the whole block.
   * @param post Desired postconditions after the whole block.
   * @param name A human-readable name for this context, used in triple labels.
   * @return
   */
  def handle(call: Stmt, before: CompositeStmt, after: CompositeStmt, pre: Seq[Expr], post: Seq[Expr], name: String): Seq[Triple] = {
    def worker(params: Seq[Id], res: Seq[Id], method: Method): Seq[Triple] = {
      // although we assume this has already been checked before during compilation
      if (params.length != method.params.length) sys.error("MethodCallHandler: Argument arity mismatch in method call")
      if (res.length != method.res.length) sys.error("MethodCallHandler: Result arity mismatch in method call")

      val paramSub: Map[Id, Id] = method.params.zip(params).toMap
      val resSub: Map[Id, Id] = method.res.zip(res).toMap
      val postSubstMap = paramSub ++ resSub

      val methodPreMapped = method.pre.map(PathBuilder.applySubstitution(_, paramSub))
      val methodPostMapped = method.post.map(PathBuilder.applySubstitution(_, postSubstMap))

      val tripleBefore = Triple(
        before,
        pre,
        methodPreMapped,
        name + " > before \"" + call + "\""
      )

      val tripleAfter = Triple(
        after,
        methodPostMapped,
        post,
        name + " > after \"" + call + "\""
      )

      List(tripleBefore, tripleAfter)
    }

    call match {
      case MultiAssignStmt(left, mce@MethodCallExpr(_, args)) => {
        worker(args, left, mce.method)
      }
      case mcs@MethodCallStmt(_, args) => {
        worker(args, Nil, mcs.method)
      }
    }
  }
}
