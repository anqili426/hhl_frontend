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
  def havoc[$: P] : P[Stmt] = P("havoc " ~ space ~ identUsed).map(e => HavocStmt(e))
  def assume[$: P] : P[Stmt] = P("assume" ~ space ~ expr).map(AssumeStmt)
  def assert[$: P] : P[Stmt] = P("assert" ~ space ~ expr).map(AssertStmt)
  def ifElse[$: P] : P[Stmt] = P("if" ~ "(" ~ expr ~ ")" ~ "{" ~ stmts ~ "}" ~ ("else" ~ "{" ~ stmts ~ "}").?).map{
    case (e, s1, s2) => IfElseStmt(e, s1, s2.getOrElse(CompositeStmt(Seq()))) }
  def whileLoop[$: P] : P[Stmt] = P("while" ~ "(" ~ expr ~ ")" ~ "{" ~ stmts ~ "}").map(loop => WhileLoopStmt(loop._1, loop._2))

  // Expressions
  def arithOp1[$: P]: P[String] = P("+" | "-" | "&&" | "!!").!
  def arithOp2[$: P]: P[String] = P("*" | "/").!
  def cmpOp[$: P]: P[String] = P("==" | "!=" | ">" | "<" | ">=" | "<=").!

  def expr[$: P]: P[Expr] = P(arithExpr ~ (cmpOp ~ expr).rep(min=0, max=1)).map{
    case (e, Nil) => e
    case (e, items) => BinaryExpr(e, items(0)._1, items(0)._2)
  }

  def arithExpr[$: P]: P[Expr] = P(arithTerm ~ (arithOp1 ~ arithExpr).rep(min=0, max=1)).map{
    case (e, Nil) => e
    case (e, items) => BinaryExpr(e, items(0)._1, items(0)._2)
  }

  def arithTerm[$: P]: P[Expr] = P(basicExpr ~ (arithOp2 ~ arithTerm).rep(min=0, max=1)).map{
    case (e, Nil) => e
    case (e, items) => BinaryExpr(e, items(0)._1, items(0)._2)
  }

  def basicExpr[$: P]: P[Expr] = P(boolean | unaryExpr | identUsed | number | "(" ~ expr ~ ")")

  def unaryExpr[$: P]: P[UnaryExpr] = P(notExpr | negExpr)
  def notExpr[$: P]: P[UnaryExpr] = P("!" ~ boolean).map(e => UnaryExpr("!", e))
  def negExpr[$: P]: P[UnaryExpr] = P("-" ~ number).map(e => UnaryExpr("-", e))

  def boolean[$: P] : P[Bool] = P(boolTrue | boolFalse)
  def boolTrue[$: P]: P[Bool] = P("true").!.map(_ => Bool(true))
  def boolFalse[$: P]: P[Bool] = P("false").!.map(_ => Bool(false))


  def identUsed[$: P]: P[Id] = P(CharIn("a-zA-Z_") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map{
    case name =>
      if (!allVars.contains(name)) throw IdentifierNotFoundException("Identifier " + name + " is not defined. ")
      Id(name)
  }

  def number[$: P]: P[Num] = P(CharIn("0-9").rep(1).!.map(_.toInt)).map(value => Num(value))
}
