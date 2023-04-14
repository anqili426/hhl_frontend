package viper.HHLVerifier

import fastparse._
import MultiLineWhitespace._


case class DuplicateIdentifierException(msg: String) extends Exception
case class IdentifierNotFoundException(msg: String) extends Exception

object Parser {
  // TODO: add symbol table to check var defined & var used
  var allVars = Map[String, String]()

  def program[$: P]: P[HHLProgram] = P(Start ~ stmts ~ End).map(s => HHLProgram(s))

  def space[$: P]: P[Unit] = P(CharsWhileIn(" \r\n", 0))

  def identNew[$: P] : P[Expr] = P(CharIn("a-zA-Z_") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => Id(name))
  def varDecl[$: P] : P[Decl] = P("var" ~ identNew.! ~ ":" ~ typeName.!).map{
    case (varName, typ) =>
      if (allVars.contains(varName)) throw DuplicateIdentifierException("Duplicate identifier " + varName)
      else allVars += varName -> typ
      PVarDecl(varName, typ)
  }

  def assertVarDecl[$: P] : P[AssertVarDecl] = P(assertVar ~ ":" ~ typeName.!).map(items => AssertVarDecl(items._1, items._2))

  def typeName[$: P] : P[Unit] = P("Int" | "Bool")

  def stmts[$: P] : P[Stmt] = P(stmt.rep).map(CompositeStmt)
  def stmt[$: P] : P[Stmt] = P(varDecl | assume | assert | ifElse | whileLoop | havoc | assign)
  def assign[$: P] : P[Stmt] = P(progVarUsed ~ ":=" ~ expr).map(e => AssignStmt(e._1, e._2))
  def havoc[$: P] : P[Stmt] = P("havoc " ~ space ~ progVarUsed).map(e => HavocStmt(e))
  def assume[$: P] : P[Stmt] = P("assume" ~ space ~ expr).map(AssumeStmt)
  def assert[$: P] : P[Stmt] = P("assert" ~ space ~ expr).map(AssertStmt)
  def ifElse[$: P] : P[Stmt] = P("if" ~ "(" ~ expr ~ ")" ~ "{" ~ stmts ~ "}" ~ ("else" ~ "{" ~ stmts ~ "}").?).map{
    case (e, s1, s2) => IfElseStmt(e, s1, s2.getOrElse(CompositeStmt(Seq()))) }
  def whileLoop[$: P] : P[Stmt] = P("while" ~ "(" ~ expr ~ ")" ~ loopInv.rep ~ "{" ~ stmts ~ "}").map {
    case (cond, Nil, s) => WhileLoopStmt(cond, s)
    case (cond, invs, s) => WhileLoopStmt(cond, s, invs)
  }
  def loopInv[$: P]: P[Expr] = P("invariant" ~ space ~ hyperAssertExpr)

  def arithOp1[$: P]: P[String] = P("+" | "-" | "&&" | "!!").!
  def arithOp2[$: P]: P[String] = P("*" | "/").!
  def impliesOp[$: P]: P[String] = P("implies").!
  def cmpOp[$: P]: P[String] = P("==" | "!=" | ">=" | "<=" | ">" | "<").!
  def quantifier[$: P]: P[String] = P("forall" | "exists").!

  def expr[$: P]: P[Expr] = P(hyperAssertExpr | otherExpr)

  def hyperAssertExpr[$: P]: P[Expr] = P(quantifier ~ (assertVarDecl).rep(sep=",", min=1) ~ "::" ~ expr).map{
    case (quant, vars, e) => {
      quant match {
        case "forall" => ForAllExpr(vars, e)
        case "exists" => ExistsExpr(vars, e)
      }
    }
  }

  def otherExpr[$: P]: P[Expr] = P(normalExpr ~ (impliesOp ~/ expr).?).map{
    case (e, None) => e
    case (e, Some(items)) => ImpliesExpr(e, items._2)
  }

  def normalExpr[$: P]: P[Expr] = P(arithExpr ~ (cmpOp ~/ normalExpr).rep(min = 0, max = 1)).map {
    case (e, Nil) => e
    case (e, items) => BinaryExpr(e, items(0)._1, items(0)._2)
  }

  def arithExpr[$: P]: P[Expr] = P(arithTerm ~ (arithOp1 ~/ arithExpr).rep(min=0, max=1)).map{
    case (e, Nil) => e
    case (e, items) => BinaryExpr(e, items(0)._1, items(0)._2)
  }

  def arithTerm[$: P]: P[Expr] = P(basicExpr ~ (arithOp2 ~/ arithTerm).rep(min=0, max=1)).map{
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

  def identUsed[$: P]: P[Expr] = P(progVarUsed | assertVar)

  def progVarUsed[$: P]: P[Id] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => Id(name))

  def assertVar[$: P]: P[AssertVar] = P("_" ~~ CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => AssertVar(name))

  def number[$: P]: P[Num] = P(CharIn("0-9").rep(1).!.map(_.toInt)).map(value => Num(value))
}
