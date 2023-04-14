package viper.HHLVerifier

import fastparse._
import MultiLineWhitespace._

object Parser {
  def program[$: P]: P[HHLProgram] = P(Start ~ stmts ~ End).map(s => HHLProgram(s))

  def spaces[$: P]: P[Unit] = P(CharIn(" \r\n\t").rep(1))

  def varDecl[$: P] : P[Decl] = P("var" ~ progVar ~ ":" ~ typeName).map(items => PVarDecl(items._1, items._2))

  def assertVarDecl[$: P] : P[AssertVarDecl] = P(assertVar ~ ":" ~ typeName).map(items => AssertVarDecl(items._1, items._2))

  def typeName[$: P] : P[Type] = P("Int" | "Bool" | "State").!.map{
    case "Int" => IntType()
    case "Bool" => BoolType()
    case "State" => State()
  }

  def stmts[$: P] : P[Stmt] = P(stmt.rep).map(CompositeStmt)
  def stmt[$: P] : P[Stmt] = P(varDecl | assume | assert | ifElse | whileLoop | havoc | assign)
  def assign[$: P] : P[Stmt] = P(progVar ~ ":=" ~ expr).map(e => AssignStmt(e._1, e._2))
  def havoc[$: P] : P[Stmt] = P("havoc" ~~ spaces ~ progVar).map(e => HavocStmt(e))
  def assume[$: P] : P[Stmt] = P("assume" ~~ spaces ~ expr).map(AssumeStmt)
  def assert[$: P] : P[Stmt] = P("assert" ~~ spaces ~ expr).map(AssertStmt)
  def ifElse[$: P] : P[Stmt] = P("if" ~ "(" ~ expr ~ ")" ~ "{" ~ stmts ~ "}" ~ ("else" ~ "{" ~ stmts ~ "}").?).map{
    case (e, s1, s2) => IfElseStmt(e, s1, s2.getOrElse(CompositeStmt(Seq()))) }
  def whileLoop[$: P] : P[Stmt] = P("while" ~ "(" ~ expr ~ ")" ~ loopInv.rep ~ "{" ~ stmts ~ "}").map {
    case (cond, Nil, s) => WhileLoopStmt(cond, s)
    case (cond, invs, s) => WhileLoopStmt(cond, s, invs)
  }
  def loopInv[$: P]: P[Expr] = P("invariant" ~~ spaces ~ hyperAssertExpr)

  def arithOp1[$: P]: P[String] = P("+" | "-" | "&&" | "!!").!
  def arithOp2[$: P]: P[String] = P("*" | "/").!
  def impliesOp[$: P]: P[String] = P("implies").!
  def cmpOp[$: P]: P[String] = P("==" | "!=" | ">=" | "<=" | ">" | "<").!
  def quantifier[$: P]: P[String] = P("forall" | "exists").!

  def expr[$: P]: P[Expr] = P(hyperAssertExpr | otherExpr)

  def hyperAssertExpr[$: P]: P[Expr] = P(quantifier ~~ spaces ~ (assertVarDecl).rep(sep=",", min=1) ~ "::" ~ expr).map{
    case (quant, vars, e) => {
      quant match {
        case "forall" => ForAllExpr(vars, e)
        case "exists" => ExistsExpr(vars, e)
      }
    }
  }

  def otherExpr[$: P]: P[Expr] = P(normalExpr ~~ (spaces ~ impliesOp ~~/ spaces ~ expr).?).map{
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

  def basicExpr[$: P]: P[Expr] = P(boolean | unaryExpr | identifier | number | "(" ~ expr ~ ")")

  def unaryExpr[$: P]: P[UnaryExpr] = P(notExpr | negExpr)
  def notExpr[$: P]: P[UnaryExpr] = P("!" ~ boolean).map(e => UnaryExpr("!", e))
  def negExpr[$: P]: P[UnaryExpr] = P("-" ~ number).map(e => UnaryExpr("-", e))

  def boolean[$: P] : P[BoolLit] = P(boolTrue | boolFalse)
  def boolTrue[$: P]: P[BoolLit] = P("true").!.map(_ => BoolLit(true))
  def boolFalse[$: P]: P[BoolLit] = P("false").!.map(_ => BoolLit(false))

  def identifier[$: P]: P[Expr] = P(progVar | assertVar)

  def progVar[$: P]: P[Id] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => Id(name))

  def assertVar[$: P]: P[AssertVar] = P("_" ~~ CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => AssertVar(name))

  def number[$: P]: P[Num] = P(CharIn("0-9").rep(1).!.map(_.toInt)).map(value => Num(value))
}
