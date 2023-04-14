package viper.HHLVerifier

sealed trait Expr
case class Id(name: String) extends Expr {
  var typ: Type = null  // To be updated during type checking
}
case class AssertVar(name: String) extends Expr {
  var typ: Type = null // To be updated during type checking
}

case class AssertVarDecl(vName: AssertVar, vType: Type) extends Expr
case class Num(value: Int) extends Expr
case class BoolLit(value: Boolean) extends Expr
case class BinaryExpr (e1: Expr, op: String, e2: Expr) extends Expr
case class UnaryExpr (op: String, e: Expr) extends Expr
case class ImpliesExpr(left: Expr, right: Expr) extends Expr
case class ForAllExpr(assertVars: Seq[AssertVarDecl], body: Expr) extends Expr
case class ExistsExpr(assertVars: Seq[AssertVarDecl], body: Expr) extends Expr

sealed trait Decl extends Stmt
case class PVarDecl(vName: Id, vType: Type) extends Decl

sealed trait Stmt
case class CompositeStmt(stmts: Seq[Stmt]) extends Stmt
case class AssignStmt(left: Id, right: Expr) extends Stmt
case class HavocStmt(id: Id) extends Stmt
case class AssumeStmt(e: Expr) extends Stmt
case class AssertStmt(e: Expr) extends Stmt
case class IfElseStmt(cond: Expr, ifStmt: Stmt, elseStmt: Stmt) extends Stmt
case class WhileLoopStmt(cond: Expr, body: Stmt, inv: Seq[Expr] =Seq(BoolLit(true))) extends Stmt

case class HHLProgram(stmts: Stmt) {
  val content: Stmt = stmts
}

sealed trait Type
case class IntType() extends Type
case class BoolType() extends Type
case class State() extends Type