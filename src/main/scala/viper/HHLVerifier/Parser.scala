package viper.HHLVerifier

import fastparse._
import JavaWhitespace._
import viper.HHLVerifier.generation.Generator


object Parser {
  // Program Structure ---------------------------------------------------------
  def program[$: P]: P[HHLProgram] = P(Start ~ method.rep ~ End).map{
    case Nil => HHLProgram(Seq.empty)
    case methods => HHLProgram(methods)
  }

  // Methods and methods utils
  def method[$: P]: P[Method] = P(Index ~ "method" ~~ spaces ~~ methodName ~ Index ~ "(" ~ methodVarDecl.rep(sep=",") ~ ")"  ~ ("returns" ~ "(" ~ methodVarDecl.rep(sep=",") ~ ")").? ~ precondition.rep ~ postcondition.rep  ~"{" ~ stmts ~ "}").map{
    items =>
      val args = if (items._4 != Nil) items._4 else Seq.empty
      val res = if (items._5 != None) items._5.get else Seq.empty
      val pre = if (items._6 != Nil) items._6 else Seq.empty
      val post = if (items._7 != Nil) items._7 else Seq.empty
      Method(items._2, args, res, pre, post, items._8, items._1, items._3)
  }
  def precondition[$: P]: P[Expr] = P("requires" ~~ spaces ~ expr)
  def postcondition[$: P]: P[Expr] = P("ensures" ~~ spaces ~ expr)
  // declaration of method parameters
  def methodVarDecl[$: P]: P[Id] = P(progVar ~ ":" ~ notStateTypeName).map{
    items =>
      items._1.typ = items._2
      items._1
  }
  def methodName[$ :P]: P[String] =  P(CharIn("a-zA-Z_") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!

  // Handling variables ---------------------------------------------------------
  // Identifiers
  def identifier[$: P]: P[Expr] = P(Index ~ (progVar | assertVar | proofVar) ~ Index).map { case (oL, id, oR) => id.setOffsets(oL, oR)}
  def progVar[$: P]: P[Id] = generalId.map(name => Id(name))
  def assertVar[$: P]: P[AssertVar] = P("_" ~~ CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => AssertVar(name))
  def proofVar[$: P]: P[ProofVar] = P("$" ~~ CharIn("a-mo-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(ProofVar)

  // Declaration
  // programming variables
  def varDecl[$: P] : P[PVarDecl] = P("var" ~ progVar ~ ":" ~ notStateTypeName).map(items => PVarDecl(items._1, items._2))
  // assert variables (start with _..., occur in assertions)
  def normalAssertVarDecl[$: P] : P[AssertVarDecl] = P(assertVar ~ ":" ~ notStateTypeName).map(items => AssertVarDecl(items._1, items._2))
  // proof variables (declared with let ..., start with $, used in statements)
  def proofVarDecl[$: P]: P[ProofVarDecl] = P(stateProofVarDeclErr | stateProofVarDecl | normalProofVarDecl)
  def normalProofVarDecl[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ proofVar ~ ":" ~ notStateTypeName ~ "::" ~ expr).map{
    items =>
      items._1.typ = items._2
      ProofVarDecl(items._1, items._3)
  }
  def stateProofVarDecl[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ "<" ~ proofVar ~ ">" ~ ("::" ~ expr).?).map {
    items =>
      items._1.typ = StateType()
      val stateExistsExpr = StateExistsExpr(items._1, false)
      val body = if (items._2.isEmpty) stateExistsExpr else BinaryExpr(stateExistsExpr, "&&", items._2.get)
      ProofVarDecl(items._1, body)
  }
  def stateProofVarDeclErr[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ "<<" ~ proofVar ~ ">>" ~ ("::" ~ expr).?).map {
    items =>
      items._1.typ = StateType()
      val stateExistsExpr = StateExistsExpr(items._1, true)
      val body = if (items._2.isEmpty) stateExistsExpr else BinaryExpr(stateExistsExpr, "&&", items._2.get)
      ProofVarDecl(items._1, body)
  }

  // Statements ---------------------------------------------------------
  def stmts[$: P] : P[CompositeStmt] = P(stmt.rep).map(CompositeStmt)
  def stmt[$: P] : P[Stmt] = P(Index ~ (varDecl | assume | assert | ifElse | whileLoop | havoc | assign | multiAssign | frame | hyperAssume | hyperAssert | proofVarDecl | useHintStmt | methodCallStmt) ~ Index).map{
    case (oL, stmt, oR) => stmt.setOffsets(oL, oR)
  }

  // Basic Statements
  def methodCall[$: P]: P[(String, Seq[Id])] = P(methodName ~ "(" ~ progVar.rep(sep=",", min=0) ~")")
  def multiAssign[$: P]: P[MultiAssignStmt] = P(progVar.rep(sep=",", min=1) ~ ":=" ~ methodCall).map(items => MultiAssignStmt(items._1, MethodCallExpr(items._2._1, items._2._2)))
  def assign[$: P] : P[AssignStmt] = P(progVar ~ ":=" ~ implicationExpr).map(e => AssignStmt(e._1, e._2))
  def havoc[$: P] : P[HavocStmt] = P("havoc" ~~ spaces ~ progVar ~ hintDecl.?).map{
    case(v, None) => HavocStmt(v, Option.empty)
    case(v, hintDecl) => HavocStmt(v, hintDecl)
  }
  def assume[$: P] : P[AssumeStmt] = P("assume" ~~ spaces ~ implicationExpr).map(AssumeStmt)
  def assert[$: P] : P[AssertStmt] = P("assert" ~~ spaces ~ implicationExpr).map(AssertStmt)
  def hyperAssume[$: P]: P[HyperAssumeStmt] = P("hyperAssume" ~~ spaces ~ expr).map(HyperAssumeStmt)
  def hyperAssert[$: P]: P[HyperAssertStmt] = P("hyperAssert" ~~ spaces ~ expr).map(HyperAssertStmt)
  def declareStmt[$: P]: P[DeclareStmt] = P("declare" ~~ spaces ~ blockId ~ "{" ~ stmts ~ "}").map(items => DeclareStmt(items._1, items._2))
  def reuseStmt[$: P]: P[ReuseStmt] = P("reuse" ~~ spaces ~ blockId).map(ReuseStmt)
  def stmtInIf[$: P]: P[Stmt] = P(stmt | declareStmt)
  def stmtsInIf[$: P]: P[CompositeStmt] = P(stmtInIf.rep).map(CompositeStmt)
  def stmtInElse[$: P]: P[Stmt] = P(stmt | reuseStmt)
  def stmtsInElse[$: P]: P[CompositeStmt] = P(stmtInElse.rep).map(CompositeStmt)
  def ifElse[$: P] : P[IfElseStmt] = P("if" ~ "(" ~ implicationExpr ~ ")" ~ "{" ~ stmtsInIf ~ "}" ~ ("else" ~ "{" ~ stmtsInElse ~ "}").?).map{
    case (e, s1, s2) => IfElseStmt(e, s1, s2.getOrElse(CompositeStmt(Seq())))
  }
  def whileLoop[$: P] : P[WhileLoopStmt] = P("while" ~~ spaces ~ ("syncRule" | "forAllExistsRule" | "existsRule" | "syncTotRule" | "desugaredRule").?.! ~ "(" ~ implicationExpr ~ ")"  ~ loopInv.rep ~ ("decreases" ~ arithExpr).? ~ "{" ~ stmts ~ "}").map {
    items =>
      val rule = if (items._1 == "" && !Generator.autoSelectRules) throw UnknownException("Each while loop must be specified with exactly one rule unless auto-selection of rules is turned on. ")
      else if (items._1 == "") "unspecified" else items._1
      val cond = items._2
      val invs = if (items._3 == Nil) Seq.empty else items._3
      val decr = if (items._4.isEmpty) Option.empty else items._4
      val body = items._5
      if (rule == "syncTotRule" && decr.isEmpty) throw UnknownException("Users must provide a decreases clause to use the syncTot Rule")
      WhileLoopStmt(cond, body, invs, decr, rule)
  }
  def frame[$: P]: P[FrameStmt] = P("frame" ~~ spaces ~ expr ~ "{" ~ stmts ~ "}").map(items => FrameStmt(items._1, items._2))
  def useHintStmt[$: P]: P[UseHintStmt] = P("use" ~~ spaces ~ expr).map(UseHintStmt)
  def methodCallStmt[$: P]: P[MethodCallStmt] = P(methodCall).map(items => MethodCallStmt(items._1, items._2))

  // Utils for statements
  def loopInv[$: P]: P[(Option[HintDecl], Expr)] = P(hintDecl.? ~ "invariant" ~~ spaces ~ expr)
  // identifies a block of code
  def blockId[$: P]: P[Id] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map{
    name =>
      val blockId = Id(name)
      blockId.typ = TypeInstance.stmtBlockType
      blockId
  }
  def hintDecl[$: P]: P[HintDecl] = P("{" ~ generalId ~ "}").map {HintDecl}

  // Expressions ---------------------------------------------------------
  // Operations in expressions
  // ranking provides precedence
  def arithOp1[$: P]: P[String] = P("+" | "-").!
  def arithOp2[$: P]: P[String] = P("*" | "/" | "%").!
  def impliesOp[$: P]: P[String] = P("==>").!
  def boolOp1[$: P]: P[String] = P("&&" | "||").!
  def boolOp2[$: P]: P[String] = P("==" ~ &(!CharIn(">")) | "!=").!
  def combinatorOps[$: P]: P[String] = P("union".! | "intersection".! | "setminus".! | "in".! ~~ spaces | "++".!) // the spaces are there to avaid a very specfic bug introduced by using cuts in compositeOpsExpr
  def cmpOp[$: P]: P[String] = P(">=" | "<=" | ">" | "<").!
  def quantifier[$: P]: P[String] = P("forall" | "exists").!

  // Assertions
  // Syntax 1: assertVar is NOT of type State -- forall n: Int :: P(n)
  // Syntax 2: assertVar is of type State -- forall <s1>: State :: P(s1)
  // Syntax 2 is translated to (forall s1: State :: <s1> ==> P)
  // This also means that <s> can only appear at this position (might affect proof var decl?)
  def assertion[$: P]: P[Expr] = P(hyperAssertionErr | hyperAssertion | normalAssertion)
  def normalAssertion[$: P]: P[Expr] = P(quantifier ~~ spaces ~ (normalAssertVarDecl).rep(sep=",", min=1) ~ "::" ~ expr).map(items => Assertion(items._1, items._2, items._3))
  def hyperAssertion[$: P]: P[Expr] = P(Index ~ quantifier ~ ("<"  ~ assertVar ~ ">").rep(sep=",", min=1) ~ "::" ~ expr ~ Index).map{
    case (oL, quantifier, assertVars, expr, oR) =>
      val assertVarDecl = assertVars.map(i => AssertVarDecl(i, StateType()))
      val allStatesExistSeq: Seq[Expr] = assertVars.map(i => StateExistsExpr(i, false))
      val body = {
        if (allStatesExistSeq.isEmpty) expr
        else {
          val allStatesExist = allStatesExistSeq.reduceLeft((e1, e2) => BinaryExpr(e1, "&&", e2))
          if (quantifier == "forall") ImpliesExpr(allStatesExist, expr)
          else BinaryExpr(allStatesExist, "&&", expr)
        }
      }
      Assertion(quantifier, assertVarDecl, body).setOffsets(oL, oR)
  }
  def hyperAssertionErr[$: P]: P[Assertion] = P(quantifier ~ ("<<" ~ assertVar ~ ">>").rep(sep = ",", min = 1) ~ "::" ~ expr).map {
    items =>
      val quantifier = items._1
      val assertVarDecl = items._2.map(i => AssertVarDecl(i, StateType()))
      val allStatesExistSeq: Seq[Expr] = items._2.map(i => StateExistsExpr(i, true))
      val body = {
        if (allStatesExistSeq.isEmpty) items._3
        else {
          val allStatesExist = allStatesExistSeq.reduceLeft((e1, e2) => BinaryExpr(e1, "&&", e2))
          if (quantifier == "forall") ImpliesExpr(allStatesExist, items._3)
          else BinaryExpr(allStatesExist, "&&", items._3)
        }
      }
      Assertion(quantifier, assertVarDecl, body)
  }

  // Recursive Expression types
  // ranking and structure provides associativity and precedence
  // encapsulating expression class
  def expr[$: P]: P[Expr] = P(Index ~ (assertion | implicationExpr) ~ Index).map { case (oL, exp, oR) => exp.setOffsets(oL, oR) }
  // highest ranking expr, provides highest precedence for implications
  def implicationExpr[$: P]: P[Expr] = P(Index ~ booleanExpr ~ (impliesOp ~/ expr).? ~ Index).map{
    case (_, e, None, _) => e
    case (oL, e, Some(items), oR) => ImpliesExpr(e, items._2).setOffsets(oL, oR)
  }
  // second-highest ranking expr, provides precedence for || &&
  def booleanExpr[$: P]: P[Expr] = P(Index ~ booleanEqualityExpr ~ (boolOp1 ~/ booleanExpr).? ~ Index).map{
    case (_, e, None, _) => e
    case (oL, e, Some(items), oR) => BinaryExpr(e, items._1, items._2).setOffsets(oL, oR)
  }
  // third-highest ranking expr, provides precedence for ==
  def booleanEqualityExpr[$: P]: P[Expr] = P(Index ~ arithCompExpr ~ (boolOp2 ~/ booleanEqualityExpr).? ~ Index).map {
    case (_, e, None, _) => e
    case (oL, e, Some(items), oR) => BinaryExpr(e, items._1, items._2).setOffsets(oL, oR)
  }
  // fourth-highest ranking expr, provides precedence for <,>,<=, ...
  def arithCompExpr[$: P]: P[Expr] = P(Index ~ arithExpr ~ (cmpOp ~/ arithCompExpr).? ~ Index).map {
    case (_, e, None, _) => e
    case (oL, e, Some(items), oR) => BinaryExpr(e, items._1, items._2).setOffsets(oL, oR)
  }
  // fifth-highest ranking expr, provides precedence for +,-
  def arithExpr[$: P]: P[Expr] = P(Index ~ arithTerm ~ (arithOp1 ~/ arithExpr).? ~ Index).map{
    case (_, e, None, _) => e
    case (oL, e, Some(items), oR) => BinaryExpr(e, items._1, items._2).setOffsets(oL, oR)
  }
  // sixth-highest ranking expr, provides precedence for *, /, ...
  def arithTerm[$: P]: P[Expr] = P(Index ~ combinatorOpExpr ~ (arithOp2 ~/ arithTerm).? ~ Index).map{
    case (_, e, None, _) => e
    case (oL, e, Some(items), oR) => BinaryExpr(e, items._1, items._2).setOffsets(oL, oR)
  }
  // seventh-highest ranking expr, containing all set operations
  def combinatorOpExpr[$: P]: P[Expr] = P(Index ~ mapUpdate ~ (combinatorOps ~/ combinatorOpExpr).? ~ Index).map{
    case (_, lhs, None, _) => lhs
    case (oL, lhs, Some(par), oR) => CombExpr(lhs, par._2, par._1).setOffsets(oL, oR)
  }
//  def accessValExpr[$: P]: P[Expr] = P(Index ~ basicExpr ~ ("[" ~/ expr ~ "]").rep.? ~ Index).map{
//    case (_, lhs, None, _) => lhs
//    case (oL, lhs, Some(l), oR) => l.foldLeft(lhs)(LookupExpr).setOffsets(oL, oR)
//  }
  def mapUpdate[$: P]: P[Expr] = P(Index ~ accessValExpr ~ ("[" ~ expr ~ ":=" ~ expr ~ "]").? ~ Index).map{
    case (_, base, None, _) => base
    case (oL, base, Some((k, v)), oR) => UpdateMapExpr(base, MapTupleExpr(k, v)).setOffsets(oL, oR)
  }
  def accessValExpr[$: P]: P[Expr] = P(Index ~ basicExpr ~ ("[" ~ expr ~ "]").? ~ Index).map{
    case (_, lhs, None, _) => lhs
    case (oL, lhs, Some(l), oR) => LookupExpr(lhs, l).setOffsets(oL, oR)
  }
  // eigth-highest ranking expr, containing all usable elements
  def basicExpr[$: P]: P[Expr] = P(compositeTypeAssign  | lengthExpr | loopIndex | proofVar | boolean | unaryExpr | useHint | identifier | number | "(" ~ expr ~ ")")

  // Basic building components and utils
  def unaryExpr[$: P]: P[UnaryExpr] = P(notExpr | negExpr)
  def notExpr[$: P]: P[UnaryExpr] = P("!" ~ accessValExpr).map(e => UnaryExpr("!", e)) // Warning: Changed "!" ~ boolean to the following in notExpr without regression testing
  def negExpr[$: P]: P[UnaryExpr] = P("-" ~ number).map(e => UnaryExpr("-", e))
  def boolean[$: P] : P[BoolLit] = P(boolTrue | boolFalse)
  def boolTrue[$: P]: P[BoolLit] = P("true").!.map(_ => BoolLit(true))
  def boolFalse[$: P]: P[BoolLit] = P("false").!.map(_ => BoolLit(false))
  // def getProgVarExpr[$: P]: P[GetValExpr] = P("get(" ~ (assertVar | proofVar) ~ "," ~ progVar ~ ")").map(items => GetValExpr(items._1, items._2))
  // def getProgVarExpr[$: P]: P[GetValExpr] = P((assertVar | proofVar) ~ "[" ~ progVar ~ "]").map(items => GetValExpr(items._1, items._2))
  def loopIndex[$: P]: P[LoopIndex] = P("$n").map(_ => LoopIndex())
  def number[$: P]: P[Num] = P(CharIn("0-9").rep(1).!.map(_.toInt)).map(value => Num(value))
  def useHint[$: P]: P[Expr] = P(Index ~ generalId ~ "(" ~ expr ~ ")" ~ Index).map { case (oL, id, expr, oR) => Hint(id, expr).setOffsets(oL, oR) }

  // Initialisation
  def compositeTypeAssign[$: P]: P[Expr] = P(seqAssignExpr | setAssignExpr | mapAssignExpr)
  def seqAssignExpr[$: P]: P[SeqAssignExpr] = P("Seq[" ~~ notStateTypeName ~~ "]" ~~ "(" ~ expr.rep(sep=",").? ~ ")").map {
    case (typ, params) =>
      val exp = SeqAssignExpr(params.getOrElse(Seq.empty))
      exp.typ = SeqType(typ)
      exp
  }
  def setAssignExpr[$: P]: P[SetAssignExpr] = P("Set[" ~~ notStateTypeName ~~ "]" ~~ "(" ~ expr.rep(sep=",").? ~ ")").map {
    case (typ, params) =>
      val exp = SetAssignExpr(params.getOrElse(Seq.empty))
      exp.typ = SetType(typ)
      exp
  }
  def mapAssignExpr[$: P]: P[MapAssignExpr] = P("Map[" ~~ notStateTypeName ~~ "," ~ notStateTypeName ~~ "]" ~~ "(" ~ mapTupleExpr.rep(sep=",").? ~ ")").map {
    case (kTyp, pTyp, params) =>
      val exp = MapAssignExpr(params.getOrElse(Seq.empty))
      exp.typ = MapType(kTyp, pTyp)
      exp
  }
  def mapTupleExpr[$: P]: P[MapTupleExpr] = P(basicExpr ~ ":=" ~ expr).map(items => MapTupleExpr(items._1, items._2))

  // Special operations
  def lengthExpr[$: P]: P[LengthExpr] = P("|" ~ expr ~ "|").map(expr => LengthExpr(expr))

  // Type Handling
  def notStateTypeName[$: P] : P[Type] = P(primitiveTypeName | seqOrSetType | mapType)

  def primitiveTypeName[$: P] : P[Type] = P("Int" | "Bool").!.map{
    case "Int" => IntType()
    case "Bool" => BoolType()
  }

  def seqOrSetType[$: P] : P[Type] = P(("Seq" | "Set").! ~~ "[" ~ notStateTypeName ~ "]").map{
    case ("Seq", t) => SeqType(t)
    case ("Set", t) => SetType(t)
    case _ => throw UnknownException("Critical error occured while passing Seq/Set type declarations")
  }

  def mapType[$: P] : P[Type] = P("Map[" ~ notStateTypeName ~~ "," ~ notStateTypeName ~ "]").map{
    case (t1, t2) => MapType(t1, t2)
  }

  // Utils ---------------------------------------------------------
  def spaces[$: P]: P[Unit] = P(CharIn(" \r\n\t").rep(1))
  def generalId[$: P]: P[String] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!
}
