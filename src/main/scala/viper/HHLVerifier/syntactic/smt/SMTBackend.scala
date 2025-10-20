package viper.HHLVerifier.syntactic.smt

trait SMTBackend {
  /**
   * Checks whether the precondition `pre` ''logically entails'' the weakest
   * precondition `wp`. This is done by utilizing using an [[SMTBackend]] to check the
   * satisfiability of <code>¬(pre ⇒ wp)</code>.
   *
   * @param pre The user-supplied precondition.
   * @param wp The weakest precondition computed by [[WeakestPrecondition.compute]]
   * @param toBeExported Whether this entailment should be included in the export `.smt2` file
   *                     (e.g. `false` for entailments checked by the [[RuleSelector]], `true` for
   *                     entailments corresponding to hyper-triples that need to be verified)
   * @return [[SMTStatus]]:
   *         <ul>
   *          <li>[[SMTStatus.Unsatisfiable]] – <code>pre ⊨ wp</code> is valid.</li>
   *          <li>[[SMTStatus.Satisfiable]] – implication does <strong>not</strong> hold .</li>
   *          <li>[[SMTStatus.Unknown]] – solver aborted.</li>
   *         </ul>
   */
  def checkEntailment(pre: viper.HHLVerifier.ast.Expr, wp: viper.HHLVerifier.ast.Expr): SMTStatus
}

sealed trait SMTStatus
object SMTStatus {
  case object Satisfiable extends SMTStatus
  case object Unsatisfiable extends SMTStatus
  case object Unknown extends SMTStatus
}

sealed trait BackendMode
object BackendMode {
  case object Z3 extends BackendMode
  case object CVC5 extends BackendMode // native CVC5 Java API
  case object CVC5Proc extends BackendMode // Run CVC5 on an .smt2 file
  case object Both extends BackendMode
}