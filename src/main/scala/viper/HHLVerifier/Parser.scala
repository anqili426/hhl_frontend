package viper.HHLVerifier

import fastparse._
import JavaWhitespace._

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

  def precondition[$: P]: P[Expr] = P("requires" ~~ spaces ~ expr)
  def postcondition[$: P]: P[Expr] = P("ensures" ~~ spaces ~ expr)

  def methodVarDecl[$: P]: P[Id] = P(progVar ~ ":" ~ notStateTypeName).map{
    items => items._1.typ = items._2
      items._1
  }
  def methodName[$ :P]: P[String] =  P(CharIn("a-zA-Z_") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!

  def spaces[$: P]: P[Unit] = P(CharIn(" \r\n\t").rep(1))

  def varDecl[$: P] : P[PVarDecl] = P("var" ~ progVar ~ ":" ~ notStateTypeName).map(items => PVarDecl(items._1, items._2))

  def assertVarDecl[$: P] : P[AssertVarDecl] = P(assertVar ~ ":" ~ anyTypeName).map(items => AssertVarDecl(items._1, items._2))

  def notStateTypeName[$: P] : P[Type] = P("Int" | "Bool").!.map{
    case "Int" => IntType()
    case "Bool" => BoolType()
  }

  def anyTypeName[$: P]: P[Type] = P("Int" | "Bool" | "State").!.map {
    case "Int" => IntType()
    case "Bool" => BoolType()
    case "State" => StateType()
  }

  def proofVarDecl[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ proofVar ~ ":" ~ anyTypeName ~ "::" ~ expr).map{
    items =>
      items._1.typ = items._2
      ProofVarDecl(items._1, items._3)
  }
  def proofVar[$: P]: P[ProofVar] = P("$" ~~ CharIn("a-mo-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(ProofVar)
  def methodCall[$: P]: P[(String, Seq[Id])] = P(methodName ~ "(" ~ progVar.rep(sep=",", min=0) ~")")

  def stmts[$: P] : P[CompositeStmt] = P(stmt.rep).map(CompositeStmt)
  def stmt[$: P] : P[Stmt] = P(varDecl | assume | assert | ifElse | whileLoop | havoc | multiAssign | assign | frame | hyperAssume | hyperAssert | proofVarDecl | useHintStmt | methodCallStmt)
  def multiAssign[$: P]: P[MultiAssignStmt] = P(progVar.rep(sep=",", min=1) ~ ":=" ~ methodCall).map{
    items => MultiAssignStmt(items._1, MethodCallExpr(items._2._1, items._2._2))
  }
  def assign[$: P] : P[AssignStmt] = P(progVar ~ ":=" ~ otherExpr).map(e => AssignStmt(e._1, e._2))
  def havoc[$: P] : P[HavocStmt] = P("havoc" ~~ spaces ~ progVar ~ hintDecl.?).map{
    case(v, None) => HavocStmt(v, Option.empty)
    case(v, hintDecl) => HavocStmt(v, hintDecl)
  }
  def assume[$: P] : P[AssumeStmt] = P("assume" ~~ spaces ~ otherExpr).map(AssumeStmt)
  def assert[$: P] : P[AssertStmt] = P("assert" ~~ spaces ~ otherExpr).map(AssertStmt)
  def hyperAssume[$: P]: P[HyperAssumeStmt] = P("hyperAssume" ~~ spaces ~ expr).map(HyperAssumeStmt)
  def hyperAssert[$: P]: P[HyperAssertStmt] = P("hyperAssert" ~~ spaces ~ expr).map(HyperAssertStmt)
  def declareStmt[$: P]: P[DeclareStmt] = P("declare" ~~ spaces ~ blockId ~ "{" ~ stmts ~ "}").map(items => DeclareStmt(items._1, items._2))
  def reuseStmt[$: P]: P[ReuseStmt] = P("reuse" ~~ spaces ~ blockId).map(ReuseStmt)
  def blockId[$: P]: P[Id] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map{
    name =>
      val blockId = Id(name)
      blockId.typ = TypeInstance.stmtBlockType
      blockId
  }
  def stmtInIf[$: P]: P[Stmt] = P(stmt | declareStmt)
  def stmtsInIf[$: P]: P[CompositeStmt] = P(stmtInIf.rep).map(CompositeStmt)
  def stmtInElse[$: P]: P[Stmt] = P(stmt | reuseStmt)
  def stmtsInElse[$: P]: P[CompositeStmt] = P(stmtInElse.rep).map(CompositeStmt)
  def ifElse[$: P] : P[IfElseStmt] = P("if" ~ "(" ~ otherExpr ~ ")" ~ "{" ~ stmtsInIf ~ "}" ~ ("else" ~ "{" ~ stmtsInElse ~ "}").?).map{
    case (e, s1, s2) => IfElseStmt(e, s1, s2.getOrElse(CompositeStmt(Seq()))) }

  def whileLoop[$: P] : P[WhileLoopStmt] = P("while" ~~ spaces ~ ("syncRule" | "forAllExistsRule" | "existsRule").?.! ~ "(" ~ otherExpr ~ ")"  ~ loopInv.rep ~ "{" ~ stmts ~ "}").map {
    items =>
      val invs = if (items._3 == Nil) Seq.empty else items._3
      val stmt = WhileLoopStmt(items._2, items._4, invs)
      stmt.rule = if (items._1 == "") "default" else items._1
      stmt
  }
  def loopInv[$: P]: P[(Option[HintDecl], Expr)] = P(hintDecl.? ~ "invariant" ~~ spaces ~ expr)

  def frame[$: P]: P[FrameStmt] = P("frame" ~~ spaces ~ expr ~ "{" ~ stmts ~ "}").map(items => FrameStmt(items._1, items._2))
  def useHintStmt[$: P]: P[UseHintStmt] = P("use" ~~ spaces ~ expr).map(UseHintStmt)
  def methodCallStmt[$: P]: P[MethodCallStmt] = P(methodCall).map(items => MethodCallStmt(items._1, items._2))

  def arithOp1[$: P]: P[String] = P("+" | "-").!
  def arithOp2[$: P]: P[String] = P("*" | "/" | "%").!
  def impliesOp[$: P]: P[String] = P("==>").!
  def boolOp1[$: P]: P[String] = P("&&" | "||").!
  def boolOp2[$: P]: P[String] = P("==" ~ &(!CharIn(">")) | "!=").!
  def cmpOp[$: P]: P[String] = P(">=" | "<=" | ">" | "<").!
  def quantifier[$: P]: P[String] = P("forall" | "exists").!

  def expr[$: P]: P[Expr] = P(assertion | otherExpr)

  def assertion[$: P]: P[Assertion] = P(quantifier ~~ spaces ~ (assertVarDecl).rep(sep=",", min=1) ~ "::" ~ expr).map(items => Assertion(items._1, items._2, items._3))

  def hintDecl[$: P]: P[HintDecl] = P("{" ~ generalId ~ "}").map {HintDecl}

  def generalId[$: P]: P[String] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!

  def otherExpr[$: P]: P[Expr] = P(normalExpr ~ (impliesOp ~/ expr).?).map{
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

  def compExpr[$: P]: P[Expr] = P(arithExpr ~ (cmpOp ~/ compExpr).?).map {
      case (e, None) => e
      case (e, Some(items)) => BinaryExpr(e, items._1, items._2)
    }

  def arithExpr[$: P]: P[Expr] = P(arithTerm ~ (arithOp1 ~/ arithExpr).?).map{
    case (e, None) => e
    case (e, Some(items)) => BinaryExpr(e, items._1, items._2)
  }

  def arithTerm[$: P]: P[Expr] = P(basicExpr ~ (arithOp2 ~/ arithTerm).?).map{
    case (e, None) => e
    case (e, Some(items)) => BinaryExpr(e, items._1, items._2)
  }

  def basicExpr[$: P]: P[Expr] = P(loopIndex | proofVar | boolean | unaryExpr | getProgVarExpr | useHint | identifier | number | stateExistsErrExpr | stateExistsExpr |  "(" ~ expr ~ ")")

  def unaryExpr[$: P]: P[UnaryExpr] = P(notExpr | negExpr)
  // Warning: Changed "!" ~ boolean to the following in notExpr without regression testing
  def notExpr[$: P]: P[UnaryExpr] = P("!" ~ expr).map(e => UnaryExpr("!", e))
  def negExpr[$: P]: P[UnaryExpr] = P("-" ~ number).map(e => UnaryExpr("-", e))

  def boolean[$: P] : P[BoolLit] = P(boolTrue | boolFalse)
  def boolTrue[$: P]: P[BoolLit] = P("true").!.map(_ => BoolLit(true))
  def boolFalse[$: P]: P[BoolLit] = P("false").!.map(_ => BoolLit(false))

  def getProgVarExpr[$: P]: P[GetValExpr] = P("get(" ~ (assertVar | proofVar) ~ "," ~ progVar ~ ")").map(items => GetValExpr(items._1, items._2))

  def stateExistsExpr[$: P]: P[StateExistsExpr] = P("<"  ~ (assertVar | proofVar) ~ ">").map(item => StateExistsExpr(item, false))
  def stateExistsErrExpr[$: P]: P[StateExistsExpr] = P("<<"  ~ (assertVar | proofVar) ~ ">>").map(item => StateExistsExpr(item, true))

  def identifier[$: P]: P[Expr] = P(progVar | assertVar | proofVar)

  def progVar[$: P]: P[Id] = generalId.map(name => Id(name))

  def assertVar[$: P]: P[AssertVar] = P("_" ~~ CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => AssertVar(name))

  def loopIndex[$: P]: P[LoopIndex] = P("$n").map(_ => LoopIndex())

  def number[$: P]: P[Num] = P(CharIn("0-9").rep(1).!.map(_.toInt)).map(value => Num(value))

  def useHint[$: P]: P[Hint] = P(generalId ~ "(" ~ expr ~ ")").map { items => Hint(items._1, items._2) }
}
