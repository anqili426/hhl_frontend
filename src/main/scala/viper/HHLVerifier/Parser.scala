package viper.HHLVerifier

import fastparse._
import MultiLineWhitespace._

object Parser {
  def program[$: P]: P[HHLProgram] = P(Start ~ method.rep ~ End).map{
    case Nil => HHLProgram(Seq.empty)
    case methods => HHLProgram(methods)
  }

  def method[$: P]: P[Method] = P("method" ~~ spaces ~~ methodName ~ "(" ~ methodVarDecl.rep(sep=",") ~ ")"  ~ ("returns" ~ "(" ~ methodVarDecl.rep(sep=",") ~ ")").? ~ precondition.rep ~ postcondition.rep  ~"{" ~ stmts ~ "}").map{
    items =>
      val args = if (items._2 != Nil) items._2 else Seq.empty
      val res = if (items._3 != None) items._3.get else Seq.empty
      val pre = if (items._4 != Nil) items._4 else Seq.empty
      val post = if (items._5 != Nil) items._5 else Seq.empty
      Method(items._1, args, res, pre, post, items._6)
  }

  def precondition[$: P]: P[Assertion] = P("requires" ~~ spaces ~ hyperAssertExpr)
  def postcondition[$: P]: P[Assertion] = P("ensures" ~~ spaces ~ hyperAssertExpr)

  def methodVarDecl[$: P]: P[Id] = P(progVar ~ ":" ~ progVartypeName).map{
    items => items._1.typ = items._2
      items._1
  }
  def methodName[$ :P]: P[String] =  P(CharIn("a-zA-Z_") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!

  def spaces[$: P]: P[Unit] = P(CharIn(" \r\n\t").rep(1))

  def varDecl[$: P] : P[PVarDecl] = P("var" ~ progVar ~ ":" ~ progVartypeName).map(items => PVarDecl(items._1, items._2))

  def assertVarDecl[$: P] : P[AssertVarDecl] = P(assertVar ~ ":" ~ assertVarTypeName).map(items => AssertVarDecl(items._1, items._2))

  def progVartypeName[$: P] : P[Type] = P("Int" | "Bool").!.map{
    case "Int" => IntType()
    case "Bool" => BoolType()
  }

  def assertVarTypeName[$: P]: P[Type] = P("Int" | "Bool" | "State").!.map {
    case "Int" => IntType()
    case "Bool" => BoolType()
    case "State" => StateType()
  }

  def stmts[$: P] : P[CompositeStmt] = P(stmt.rep).map(CompositeStmt)
  def stmt[$: P] : P[Stmt] = P(varDecl | assume | assert | ifElse | whileLoop | havoc | assign)
  def assign[$: P] : P[AssignStmt] = P(progVar ~ ":=" ~ expr).map(e => AssignStmt(e._1, e._2))
  def havoc[$: P] : P[HavocStmt] = P("havoc" ~~ spaces ~ progVar).map(e => HavocStmt(e))
  def assume[$: P] : P[AssumeStmt] = P("assume" ~~ spaces ~ expr).map(AssumeStmt)
  def assert[$: P] : P[AssertStmt] = P("assert" ~~ spaces ~ expr).map(AssertStmt)
  def ifElse[$: P] : P[IfElseStmt] = P("if" ~ "(" ~ expr ~ ")" ~ "{" ~ stmts ~ "}" ~ ("else" ~ "{" ~ stmts ~ "}").?).map{
    case (e, s1, s2) => IfElseStmt(e, s1, s2.getOrElse(CompositeStmt(Seq()))) }
  def whileLoop[$: P] : P[WhileLoopStmt] = P("while" ~ "(" ~ expr ~ ")" ~ frameInv.rep ~ loopInv.rep ~ "{" ~ stmts ~ "}").map {
    items =>
      val frameInv = if (items._2 == Nil) Seq.empty else items._2
      val invs = if (items._3 == Nil) Seq.empty else items._3
      WhileLoopStmt(items._1, items._4, invs, frameInv)
  }
  def loopInv[$: P]: P[Assertion] = P("invariant" ~~ spaces ~ hyperAssertExpr)
  def frameInv[$: P]: P[Assertion] = P("frame" ~~ spaces ~ hyperAssertExpr)

  def arithOp1[$: P]: P[String] = P("+" | "-").!
  def arithOp2[$: P]: P[String] = P("*" | "/" | "%").!
  def impliesOp[$: P]: P[String] = P("==>").!
  def boolOp1[$: P]: P[String] = P("&&" | "||").!
  def boolOp2[$: P]: P[String] = P("==" ~ &(!CharIn(">")) | "!=").!
  def cmpOp[$: P]: P[String] = P(">=" | "<=" | ">" | "<").!
  def quantifier[$: P]: P[String] = P("forall" | "exists").!

  def expr[$: P]: P[Expr] = P(hyperAssertExpr | otherExpr)

  def hyperAssertExpr[$: P]: P[Assertion] = P(quantifier ~~ spaces ~ (assertVarDecl).rep(sep=",", min=1) ~ "::" ~ expr).map(
    items => Assertion(items._1, items._2, items._3))

  def otherExpr[$: P]: P[Expr] = P(normalExpr ~ (impliesOp ~/ otherExpr).?).map{
      case (e, None) => e
      case (e, Some(items)) => ImpliesExpr(e, items._2)
    }

  def normalExpr[$: P]: P[Expr] = P(eqExpr ~ (boolOp1 ~/ normalExpr).?).map{
    case (e, None) => e
    case (e, Some(items)) => BinaryExpr(e, items._1, items._2)
  }

  def eqExpr[$: P]: P[Expr] = P(compExpr ~ (boolOp2 ~/ eqExpr).?).map {
    case (e, None) => e
    case (e, Some(items)) => BinaryExpr(e, items._1, items._2)
  }

  def compExpr[$: P]: P[Expr] = P(arithExpr ~ (cmpOp ~/ compExpr).rep(min = 0, max = 1)).map {
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

  def basicExpr[$: P]: P[Expr] = P(loopIndex | boolean | unaryExpr | getProgVarExpr | identifier | number | stateExistsExpr | "(" ~ expr ~ ")")

  def unaryExpr[$: P]: P[UnaryExpr] = P(notExpr | negExpr)
  def notExpr[$: P]: P[UnaryExpr] = P("!" ~ boolean).map(e => UnaryExpr("!", e))
  def negExpr[$: P]: P[UnaryExpr] = P("-" ~ number).map(e => UnaryExpr("-", e))

  def boolean[$: P] : P[BoolLit] = P(boolTrue | boolFalse)
  def boolTrue[$: P]: P[BoolLit] = P("true").!.map(_ => BoolLit(true))
  def boolFalse[$: P]: P[BoolLit] = P("false").!.map(_ => BoolLit(false))

  def getProgVarExpr[$: P]: P[GetValExpr] = P("get(" ~ assertVar ~ "," ~ progVar ~ ")").map(items => GetValExpr(items._1, items._2))

  def stateExistsExpr[$: P]: P[StateExistsExpr] = P("<" ~ assertVar ~ ">").map(StateExistsExpr)

  def identifier[$: P]: P[Expr] = P(progVar | assertVar)

  def progVar[$: P]: P[Id] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => Id(name))

  def assertVar[$: P]: P[AssertVar] = P("_" ~~ CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => AssertVar(name))

  def loopIndex[$: P]: P[LoopIndex] = P("$n").map(_ => LoopIndex())
  def number[$: P]: P[Num] = P(CharIn("0-9").rep(1).!.map(_.toInt)).map(value => Num(value))
}
