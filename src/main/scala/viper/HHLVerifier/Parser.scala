package viper.HHLVerifier

import fastparse._
import MultiLineWhitespace._


case class DuplicateIdentifierException(msg: String) extends Exception
case class IdentifierNotFoundException(msg: String) extends Exception

object Parser {
  // TODO: add symbol table to check var defined & var used
  var allVars = Map[String, String]()

  def program[$: P]: P[HHLProgram] = P(stmts ~ End).map(s => HHLProgram(s))

  def space[$: P]: P[Unit] = P(CharsWhileIn(" \r\n", 0))

  def identNew[$: P] : P[Expr] = P(CharIn("a-zA-Z_") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => Id(name))
  def varDecl[$: P] : P[Decl] = P("var" ~ identNew.! ~ ":" ~ typeName.!).map{
    case (varName, typ) =>
      if (allVars.contains(varName)) throw DuplicateIdentifierException("Duplicate identifier " + varName)
      else allVars += varName -> typ
      VarDecl(varName, typ)
  }
  def typeName[$: P] : P[Unit] = P("Int" | "Bool")

  def stmts[$: P] : P[Stmt] = P(stmt.rep).map(CompositeStmt)
  def stmt[$: P] : P[Stmt] = P(varDecl | assume | assert | ifElse | whileLoop | havoc | assign)
  def assign[$: P] : P[Stmt] = P(identUsed ~ ":=" ~ expr).map(e => AssignStmt(e._1, e._2))
  def havoc[$: P] : P[Stmt] = P(identUsed ~ ":=" ~ nonDet).map(e => HavocStmt(e._1, e._2))
  def assume[$: P] : P[Stmt] = P("assume" ~ space ~ expr).map(AssumeStmt)
  def assert[$: P] : P[Stmt] = P("assert" ~ space ~ expr).map(AssertStmt)
  def ifElse[$: P] : P[Stmt] = P("if" ~ "(" ~ expr ~ ")" ~ "{" ~ stmts ~ "}" ~ ("else" ~ "{" ~ stmts ~ "}").?).map{
    case (e, s1, s2) => IfElseStmt(e, s1, s2.getOrElse(CompositeStmt(Seq()))) }
  def whileLoop[$: P] : P[Stmt] = P("while" ~ "(" ~ expr ~ ")" ~ "{" ~ stmts ~ "}").map(loop => WhileLoopStmt(loop._1, loop._2))

  def expr[$: P]: P[Expr] = P(prefixExpr ~ (binaryExpr).rep(min = 0, max = 1)).map {
    case (e, Nil) => e
    case (e, items) => BinaryExpr(e, items(0)._1, items(0)._2)
  }

  def binaryExpr[$: P]: P[(String, Expr)]= P(binaryOp ~ expr)

  def binaryOp[$: P]: P[String] = P("+" | "-" | "*" | "/" | "&&" | "||" | "==" | ">" | "<" | ">" | "<" | ">=" | "<=").!

  def prefixExpr[$: P]: P[Expr] = P(boolean | unaryExpr | nonDet | identUsed | number)

  def unaryExpr[$: P]: P[Expr] = P(notExpr | negExpr)
  def notExpr[$: P]: P[Expr] = P("!" ~ boolean).map(e => UnaryExpr("!", e))
  def negExpr[$: P]: P[Expr] = P("-" ~ number).map(e => UnaryExpr("-", e))

  def boolean[$: P] : P[Expr] = P(boolTrue | boolFalse)
  def boolTrue[$: P]: P[Expr] = P("true").!.map(_ => Bool(true))
  def boolFalse[$: P]: P[Expr] = P("false").!.map(_ => Bool(false))

  def nonDet[$: P]: P[Expr] = P("nonDet()").!.map(_ => Havoc())

  def identUsed[$: P]: P[Expr] = P(CharIn("a-zA-Z_") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map{
    case name =>
      if (!allVars.contains(name)) throw IdentifierNotFoundException("Identifier " + name + " is not defined. ")
      Id(name)
  }

  def number[$: P]: P[Expr] = P(CharIn("0-9").rep(1).!.map(_.toInt)).map(value => Num(value))
}
