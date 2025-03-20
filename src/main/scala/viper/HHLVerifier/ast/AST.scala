package viper.HHLVerifier.ast

import viper.HHLVerifier.management.PrettyPrinter
import viper.HHLVerifier.typing._

/** Trait for adding data used in generating error messages */
trait ErrorData {
  /** Start of expression in the source code */
  var offsetLeft = -1
  /** End of expression in the source code */
  var offsetRight = -1

  /** Set the positions of an expression in the source code.
   *
   * @tparam T return type
   * @return returns the instance itself */
  protected def setOffsets[T](left: Int, right: Int): T = {
    offsetLeft = left
    offsetRight = right
    this.asInstanceOf[T]
  }
}

/** Superclass for all expressions and assertions */
sealed class Expr() extends ErrorData {
  /** Type of the expression.
   *
   * This is the type which is used if this expression will be assigned to the variables. */
  var typ: Type = UnknownType() // Actual type of expression (i.e. type in viper)
  /** Base Type of the expression. Only set for composite objects.
   *
   * The exact meaning of this type is tricky. It is used when further information is needed to translate
   * operations with composite objects. For example, for intSeq[0] the type is Int, while the base type is Seq[Int] */
  var baseType: Type = UnknownType() // Additional type information needed to generate (e.g. type of map from which value is accessed)

  /** Relates an expression to an earlier, untransformed expression
   * used in the generator */
  var debugId: Option[Int] = None

  def setOffsets: (Int, Int) => Expr =
    setOffsets[Expr]

  override def toString: String =
    PrettyPrinter.formatExpr(this)
}

/** Identifiers for non-program variables */
class SpecialId(name: String) extends Expr {
  val idName: String = name
}

/** Identifier object for the compiler.
 *
 * @param name name of the identifier, has to be unique */
case class Id(name: String) extends Expr
/** State variable used in Assertions
 *
 * @param name name of the identifier, has to be unique */
case class AssertVar(name: String) extends SpecialId(name)
/** Proof variable used in Expressions
 *
 * @param name name of the identifier, has to be unique */
case class ProofVar(name: String) extends SpecialId(name)
/** Declaration of an Assert variable */
case class AssertVarDecl(vName: AssertVar, vType: Type) extends Expr
/** Numerical literal */
case class Num(value: Int) extends Expr
/** Boolean Literal */
case class BoolLit(value: Boolean) extends Expr
/** Two expressions combined by an operator
 *
 * @param e1 first expression
 * @param op operator as string
 * @param e2 second expression
 */
case class BinaryExpr (e1: Expr, op: String, e2: Expr) extends Expr
/** Expression with applied unary operator
 *
 * @param op operator
 * @param e expression
 */
case class UnaryExpr (op: String, e: Expr) extends Expr
/** Two expressions chained by an implication */
case class ImpliesExpr(left: Expr, right: Expr) extends Expr
/** Contains an encoded assertion with a quantifier, assertion variable declarations and an expression
 *
 * @param quantifier quantitifer encoded as a string
 * @param assertVarDecls list of assert variable declarations
 * @param body expression
 */
case class Assertion(quantifier: String, assertVarDecls: Seq[AssertVarDecl], body: Expr) extends Expr {
  var proForAll: Boolean = false
  var topExists: Boolean = false
  var triggers: Seq[Seq[StateExistsExpr]] = Seq.empty
}
case class StateExistsExpr(state: SpecialId, err: Boolean) extends Expr {
  // When useForAll is true, <_s> is translated to in_set_forall(_s, S) later
  // Otherwise, it is translated to in_set_exists(_s, S)
  var useForAll: Boolean = false
  // When useLimited is true, <_s> is translated to in_set_exists_limited(_s, S) or in_set_forall_limited(_s, S)
  var useLimited: Boolean = false
}
/** Tracks different loops */
case class LoopIndex() extends Expr
/** Declares a hint */
case class HintDecl(name: String) extends Expr
/** Encodes a hint */
case class Hint(name: String, arg: Expr) extends Expr

/**
 * Encodes a call to a method
 *
 * @param methodName method identifier
 * @param args identifiers of Hypra variables
 */
case class MethodCallExpr(methodName: String, args: Seq[Id]) extends Expr {
  var method: Method = null
  var paramsToArgs: Map[String, String] = Map.empty
}

/** Creates a new sequence  */
case class SeqAssignExpr(elements: Seq[Expr]) extends Expr
/** Creates a new set  */
case class SetAssignExpr(elements: Seq[Expr]) extends Expr
/** Creates a new map  */
case class MapAssignExpr(elements: Seq[MapTupleExpr]) extends Expr
/** Accesses a value in a complex type  */
case class LookupExpr(id: Expr, index: Expr) extends Expr
/** Returns the size / length of a complex type  */
case class LengthExpr(id: Expr) extends Expr
/** Applies an operation to two composite types */
case class CombExpr(lhs: Expr, rhs: Expr, op: String) extends Expr
/** Updates a map */
case class UpdateMapExpr(id: Expr, update: MapTupleExpr) extends Expr
/** Util object to encode map updates */
case class MapTupleExpr(k: Expr, v: Expr) extends Expr

/** Superclass for all statements */
sealed trait Stmt extends ErrorData {
  /** Contains lookup accesses performed in a statement */
  var lookUpAccesses: Seq[LookupExpr] = Seq.empty
  /** Contains all method calls performed in a statement */
  var methodCalls: Seq[MethodCallExpr] = Seq.empty

  def setOffsets: (Int, Int) => Stmt =
    setOffsets[Stmt]

  override def toString: String =
    PrettyPrinter.formatStmt(this)
}


case class CompositeStmt(stmts: Seq[Stmt]) extends Stmt {
  /** This map stores all the program variables used in this CompositeStmt object
   * It is filled in the SymbolChecker
   * Used as arguments when creating the method to verify a loop invariant */
  var allProgVars: Map[String, Type] = Map.empty
  /** Used when checking if a frame contains program variables that are modified */
  var modifiedProgVars: Map[String, Type] = Map.empty
}
/** Encodes an assignment to a variable */
case class AssignStmt(left: Id, right: Expr) extends Stmt
/** Encodes an assignment to at least a variable after a method call */
case class MultiAssignStmt(left: Seq[Id], right: MethodCallExpr) extends Stmt
/** Randomly initializes a variable */
case class HavocStmt(id: Id, hintDecl: Option[HintDecl]) extends Stmt
/** Assumes an expression */
case class AssumeStmt(e: Expr) extends Stmt
/** Asserts an expression */
case class AssertStmt(e: Expr) extends Stmt
/** Assumes a hyper expression */
case class HyperAssumeStmt(e: Expr) extends Stmt
/** Asserts a hyper expression */
case class HyperAssertStmt(e: Expr) extends Stmt
/** Encodes an if-else statement */
case class IfElseStmt(cond: Expr, ifStmt: CompositeStmt, elseStmt: CompositeStmt) extends Stmt
/** Encodes a while loop */
case class WhileLoopStmt(cond: Expr, body: CompositeStmt, inv: Seq[(Option[HintDecl], Expr)], decr: Option[Expr], rule: String = "unspecified") extends Stmt {
  // This is true if
  // 1. The loop body contains no assume statements
  // 2. The loop itself has a decreases clause
  // 3. All the loops nested in the loop body have a decreases clause
  var isTotal = !decr.isEmpty
}
/** Declares a programming variable */
case class PVarDecl(vName: Id, vType: Type) extends Stmt
/** Declares a proof variable */
case class ProofVarDecl(proofVar: ProofVar, p: Expr) extends Stmt
/** Encodes a frame statement */
case class FrameStmt(framedAssertion: Expr, body: CompositeStmt) extends Stmt
/** Encodes a declare statement */
case class DeclareStmt(blockName: Id, stmts: CompositeStmt) extends Stmt
/** Encodes a reuse statement */
case class ReuseStmt(blockName: Id) extends Stmt {
  var reusedBlock: CompositeStmt = CompositeStmt(Seq.empty)
}
/** Encodes the usage of a hint */
case class UseHintStmt(hint: Expr) extends Stmt
/** Encodes a method call in a statement */
case class MethodCallStmt(methodName: String, args: Seq[Id]) extends Stmt {
  var method: Method = null
  var paramsToArgs: Map[String, String] = Map.empty
}

/**
 * Encodes a method
 * @param mName identifier
 * @param params parameters
 * @param res return values
 * @param pre precondition
 * @param post postconditions
 * @param body method body
 */
case class Method(mName: String, params: Seq[Id], res: Seq[Id], pre: Seq[Expr], post: Seq[Expr], body: CompositeStmt) extends ErrorData {
  val paramsMap: Map[String, Type] = params.map(arg => (arg.name -> arg.typ)).toMap
  val resMap: Map[String, Type] = res.map(res => (res.name -> res.typ)).toMap
  var allVars: Map[String, Type] = Map.empty

  def setOffsets: (Int, Int) => Method = setOffsets[Method]
}

/**
 * Hypra AST object
 * @param methods all methods in the program
 */
case class HHLProgram(methods: Seq[Method]) {
  val content = methods
}