package viper.HHLVerifier

class Expr(){
  var typ: Type = UnknownType()
}

case class Id(name: String) extends Expr
case class AssertVar(name: String) extends Expr
case class AssertVarDecl(vName: AssertVar, vType: Type) extends Expr
case class Num(value: Int) extends Expr
case class BoolLit(value: Boolean) extends Expr
case class BinaryExpr (e1: Expr, op: String, e2: Expr) extends Expr
case class UnaryExpr (op: String, e: Expr) extends Expr
case class ImpliesExpr(left: Expr, right: Expr) extends Expr
case class Assertion(quantifier: String, assertVarDecls: Seq[AssertVarDecl], body: Expr) extends Expr {
  var hasStateVar = assertVarDecls.exists(decl => decl.vType.isInstanceOf[StateType])
}
case class GetValExpr(state: AssertVar, id: Id) extends Expr
case class StateExistsExpr(state: AssertVar) extends Expr
case class LoopIndex() extends Expr

sealed trait Decl extends Stmt
case class PVarDecl(vName: Id, vType: Type) extends Decl

sealed trait Stmt
case class CompositeStmt(stmts: Seq[Stmt]) extends Stmt {
  // This map stores all the program variables used in stmts
  // It is filled in the SymbolChecker
  var allProgVars: Map[String, Type] = Map.empty
}
case class AssignStmt(left: Id, right: Expr) extends Stmt
case class HavocStmt(id: Id) extends Stmt
case class AssumeStmt(e: Expr) extends Stmt
case class AssertStmt(e: Expr) extends Stmt
case class IfElseStmt(cond: Expr, ifStmt: Stmt, elseStmt: Stmt) extends Stmt
case class WhileLoopStmt(cond: Expr, body: CompositeStmt, inv: Seq[Assertion]) extends Stmt
case class RequiresStmt(e: Assertion) extends Stmt
case class EnsuresStmt(e: Assertion) extends Stmt

case class HHLProgram(stmts: Stmt) {
  val content: Stmt = stmts
}

sealed trait Type
case class UnknownType() extends Type
case class IntType() extends Type
case class BoolType() extends Type
case class StateType() extends Type

object TypeInstance {
  val unknownType = UnknownType()
  val boolType = BoolType()
  val intType = IntType()
  val stateType = StateType()
}

