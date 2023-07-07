package viper.HHLVerifier

class Expr(){
  var typ: Type = UnknownType()
}

// Identifiers that may have type State
class SpecialId(name: String) extends Expr {
  val idName: String = name
}

case class Id(name: String) extends Expr
case class AssertVar(name: String) extends SpecialId(name)
case class ProofVar(name: String) extends SpecialId(name)
case class AssertVarDecl(vName: AssertVar, vType: Type) extends Expr
case class Num(value: Int) extends Expr
case class BoolLit(value: Boolean) extends Expr
case class BinaryExpr (e1: Expr, op: String, e2: Expr) extends Expr
case class UnaryExpr (op: String, e: Expr) extends Expr
case class ImpliesExpr(left: Expr, right: Expr) extends Expr
case class HyperAssertion(hintDecl: Option[HintDecl], quantifier: String, assertVarDecls: Seq[AssertVarDecl], body: Expr) extends Expr
case class GetValExpr(state: SpecialId, id: Id) extends Expr
case class StateExistsExpr(state: SpecialId) extends Expr
case class LoopIndex() extends Expr
case class HintDecl(name: String, args: Seq[(String, Type)]) extends Expr
case class Hint(name: String, args: Seq[Expr]) extends Expr

sealed trait Stmt
case class CompositeStmt(stmts: Seq[Stmt]) extends Stmt {
  // This map stores all the program variables used in this CompositeStmt object
  // It is filled in the SymbolChecker
  // Used as arguments when creating the method to verify a loop invariant
  var allProgVars: Map[String, Type] = Map.empty
  // Used when checking if a frame contains program variables that are modified
  var modifiedProgVars: Map[String, Type] = Map.empty
}
case class AssignStmt(left: Id, right: Expr) extends Stmt
case class HavocStmt(id: Id) extends Stmt
case class AssumeStmt(e: Expr) extends Stmt
case class AssertStmt(e: Expr) extends Stmt
case class HyperAssumeStmt(e: Expr) extends Stmt
case class HyperAssertStmt(e: Expr) extends Stmt
case class IfElseStmt(cond: Expr, ifStmt: CompositeStmt, elseStmt: CompositeStmt) extends Stmt
case class WhileLoopStmt(cond: Expr, body: CompositeStmt, inv: Seq[HyperAssertion]) extends Stmt
case class PVarDecl(vName: Id, vType: Type) extends Stmt
case class ProofVarDecl(proofVar: ProofVar, p: Expr) extends Stmt
case class FrameStmt(framedAssertion: HyperAssertion, body: CompositeStmt) extends Stmt
case class DeclareStmt(blockName: Id, stmts: CompositeStmt) extends Stmt
case class ReuseStmt(blockName: Id) extends Stmt {
  var reusedBlock: CompositeStmt = CompositeStmt(Seq.empty)
}

sealed trait TopLevelDecl
case class Method(mName: String, args: Seq[Id], res: Seq[Id], pre: Seq[HyperAssertion], post: Seq[HyperAssertion], body: CompositeStmt) extends TopLevelDecl {
  val argsMap: Map[String, Type] = args.map(arg => (arg.name -> arg.typ)).toMap
  val resMap: Map[String, Type] = res.map(res => (res.name -> res.typ)).toMap
  var allVars: Map[String, Type] = Map.empty
}

case class HHLProgram(methods: Seq[Method]) {
  val content = methods
}

sealed trait Type
case class UnknownType() extends Type
case class IntType() extends Type
case class BoolType() extends Type
case class StateType() extends Type
case class StmtBlockType() extends Type

object TypeInstance {
  val unknownType = UnknownType()
  val boolType = BoolType()
  val intType = IntType()
  val stateType = StateType()
  val stmtBlockType = StmtBlockType()
}

