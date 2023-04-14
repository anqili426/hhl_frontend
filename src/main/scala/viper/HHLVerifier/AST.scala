package viper.HHLVerifier

sealed trait Expr
case class Id(name: String) extends Expr
case class AssertVar(name: String) extends Expr
case class AssertVarDecl(vName: AssertVar, vType: String) extends Expr
case class Num(value: Int) extends Expr
case class Bool(value: Boolean) extends Expr
case class BinaryExpr (e1: Expr, op: String, e2: Expr) extends Expr
case class UnaryExpr (op: String, e: Expr) extends Expr
case class ImpliesExpr(left: Expr, right: Expr) extends Expr
case class ForAllExpr(assertVars: Seq[AssertVarDecl], body: Expr) extends Expr
case class ExistsExpr(assertVars: Seq[AssertVarDecl], body: Expr) extends Expr

sealed trait Decl extends Stmt
case class PVarDecl(vName: String, vType: String) extends Decl

sealed trait Stmt
case class CompositeStmt(stmts: Seq[Stmt]) extends Stmt
case class AssignStmt(left: Id, right: Expr) extends Stmt
case class HavocStmt(id: Id) extends Stmt
case class AssumeStmt(e: Expr) extends Stmt
case class AssertStmt(e: Expr) extends Stmt
case class IfElseStmt(cond: Expr, ifStmt: Stmt, elseStmt: Stmt) extends Stmt
case class WhileLoopStmt(cond: Expr, body: Stmt, inv: Seq[Expr] =Seq(Bool(true))) extends Stmt

case class HHLProgram(stmts: Stmt) {
  val content: Stmt = stmts
}