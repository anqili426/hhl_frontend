package viper.HHLVerifier

sealed trait Expr
case class Id(name: String) extends Expr
case class Num(value: Int) extends Expr
case class Bool(value: Boolean) extends Expr
case class Havoc() extends Expr
case class BinaryExpr (e1: Expr, op: String, e2: Expr) extends Expr
case class UnaryExpr (op: String, e: Expr) extends Expr

sealed trait Decl extends Stmt
case class VarDecl(vName: String, vType: String) extends Decl

sealed trait Stmt
case class CompositeStmt(stmts: Seq[Stmt]) extends Stmt
case class AssignStmt(left: Expr, right: Expr) extends Stmt
case class HavocStmt(left: Expr, right: Expr) extends Stmt
case class AssumeStmt(e: Expr) extends Stmt
case class AssertStmt(e: Expr) extends Stmt
case class IfElseStmt(cond: Expr, ifStmt: Stmt, elseStmt: Stmt) extends Stmt
case class WhileLoopStmt(cond: Expr, body: Stmt) extends Stmt

case class HHLProgram(stmts: Stmt) {
  val content: Stmt = stmts
}