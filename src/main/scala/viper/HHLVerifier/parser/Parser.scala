package viper.HHLVerifier.parser

import fastparse.JavaWhitespace._
import fastparse._
import viper.HHLVerifier.parser.Mappings._
import viper.HHLVerifier._

object Parser {
  // Program Structure
  def program[$: P]: P[HHLProgram] = P(Start ~ method.rep ~ End).map(mapProgram)

  // Methods and methods utils
  def method[$: P]: P[Method] = P(Index ~ "method" ~~ spaces ~~ methodName ~ Index ~ "(" ~ methodVarDecl.rep(sep=",") ~ ")"  ~ ("returns" ~ "(" ~ methodVarDecl.rep(sep=",") ~ ")").? ~ precondition.rep ~ postcondition.rep  ~"{" ~ stmts ~ "}").map(mapMethod)
  def precondition[$: P]: P[Expr] = P("requires" ~~ spaces ~ expr)
  def postcondition[$: P]: P[Expr] = P("ensures" ~~ spaces ~ expr)
  def methodName[$: P]: P[String] = P(CharIn("a-zA-Z_") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!
  def methodVarDecl[$: P]: P[Id] = P(progVar ~ ":" ~ notStateTypeName).map(mapMethodVarDecl)

  // Variables and Declarations
  def identifier[$: P]: P[Expr] = P(Index ~ (progVar | assertVar | proofVar) ~ Index).map { case (oL, id, oR) => mapIdentifier(oL, id, oR) }
  
  // programming variables
  def progVar[$: P]: P[Id] = generalId.map(name => Id(name))
  def varDecl[$: P] : P[PVarDecl] = P("var" ~ progVar ~ ":" ~ notStateTypeName).map(mapVarDecl)

  // assert variables (start with _..., occur in assertions)
  def assertVar[$: P]: P[AssertVar] = P("_" ~~ CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => AssertVar(name))
  def normalAssertVarDecl[$: P] : P[AssertVarDecl] = P(assertVar ~ ":" ~ notStateTypeName).map(mapNormalAssertVarDecl)

  // proof variables (declared with let ..., start with $, used in statements)
  def proofVar[$: P]: P[ProofVar] = P("$" ~~ CharIn("a-mo-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(ProofVar)
  def proofVarDecl[$: P]: P[ProofVarDecl] = P(stateProofVarDeclErr | stateProofVarDecl | normalProofVarDecl)
  def normalProofVarDecl[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ proofVar ~ ":" ~ notStateTypeName ~ "::" ~ expr).map(mapNormalProofVarDecl)
  def stateProofVarDecl[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ "<" ~ proofVar ~ ">" ~ ("::" ~ expr).?).map(mapStateProofVarDecl)
  def stateProofVarDeclErr[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ "<<" ~ proofVar ~ ">>" ~ ("::" ~ expr).?).map(mapStateProofVarDeclErr)

  // Statements ---------------------------------------------------------
  def stmts[$: P] : P[CompositeStmt] = P(stmt.rep).map(CompositeStmt)
  def stmt[$: P] : P[Stmt] = P(Index ~ (
    varDecl | proofVarDecl |
    assign | multiAssign | methodCallStmt |
    ifElse | whileLoop |
    assume | assert | havoc | frame | hyperAssume | hyperAssert | useHintStmt
  ) ~ Index).map { case (oL, stmt, oR) => mapStmt(oL, stmt, oR) }

  def methodCall[$: P]: P[(String, Seq[Id])] = P(methodName ~ "(" ~ progVar.rep(sep=",", min=0) ~")")
  def multiAssign[$: P]: P[MultiAssignStmt] = P(progVar.rep(sep=",", min=1) ~ ":=" ~ methodCall).map(mapMultiAssign)
  def assign[$: P] : P[AssignStmt] = P(progVar ~ ":=" ~ implicationExpr).map(mapAssign)
  def havoc[$: P] : P[HavocStmt] = P("havoc" ~~ spaces ~ progVar ~ hintDecl.?).map { case (v, hintDecl) => mapHavoc(v, hintDecl) }
  def assume[$: P] : P[AssumeStmt] = P("assume" ~~ spaces ~ normalAssertion).map(mapAssume)
  def assert[$: P] : P[AssertStmt] = P("assert" ~~ spaces ~ normalAssertion).map(mapAssert)
  def hyperAssume[$: P]: P[HyperAssumeStmt] = P("hyperAssume" ~~ spaces ~ expr).map(mapHyperAssume)
  def hyperAssert[$: P]: P[HyperAssertStmt] = P("hyperAssert" ~~ spaces ~ expr).map(mapHyperAssert)
  def declareStmt[$: P]: P[DeclareStmt] = P("declare" ~~ spaces ~ blockId ~ "{" ~ stmts ~ "}").map(mapDeclareStmt)
  def reuseStmt[$: P]: P[ReuseStmt] = P("reuse" ~~ spaces ~ blockId).map(mapReuseStmt)
  def stmtInIf[$: P]: P[Stmt] = P(stmt | declareStmt)
  def stmtsInIf[$: P]: P[CompositeStmt] = P(stmtInIf.rep).map(CompositeStmt)
  def stmtInElse[$: P]: P[Stmt] = P(stmt | reuseStmt)
  def stmtsInElse[$: P]: P[CompositeStmt] = P(stmtInElse.rep).map(CompositeStmt)
  def ifElse[$: P] : P[IfElseStmt] = P("if" ~ "(" ~ implicationExpr ~ ")" ~ "{" ~ stmtsInIf ~ "}" ~ ("else" ~ "{" ~ stmtsInElse ~ "}").?).map { case (e, s1, s2) => mapIfElse(e, s1, s2) }
  def whileLoop[$: P] : P[WhileLoopStmt] = P("while" ~~ spaces ~ ("syncRule" | "forAllExistsRule" | "existsRule" | "syncTotRule" | "desugaredRule").?.! ~ "(" ~ implicationExpr ~ ")"  ~ loopInv.rep ~ ("decreases" ~ arithExpr).? ~ "{" ~ stmts ~ "}").map(mapWhileLoop)
  def frame[$: P]: P[FrameStmt] = P("frame" ~~ spaces ~ expr ~ "{" ~ stmts ~ "}").map(mapFrame)
  def useHintStmt[$: P]: P[UseHintStmt] = P("use" ~~ spaces ~ expr).map(mapUseHintStmt)
  def methodCallStmt[$: P]: P[MethodCallStmt] = P(methodCall).map(mapMethodCallStmt)

  // Utils for statements
  def loopInv[$: P]: P[(Option[HintDecl], Expr)] = P(hintDecl.? ~ "invariant" ~~ spaces ~ expr)
  def blockId[$: P]: P[Id] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(mapBlockId)
  def hintDecl[$: P]: P[HintDecl] = P("{" ~ generalId ~ "}").map(HintDecl)

  // Expressions
  // operations in expressions
  def arithOp1[$: P]: P[String] = P("+" | "-").!
  def arithOp2[$: P]: P[String] = P("*" | "/" | "%").!
  def impliesOp[$: P]: P[String] = P("==>").!
  def boolOp1[$: P]: P[String] = P("&&" | "||").!
  def boolOp2[$: P]: P[String] = P("==" ~ &(!CharIn(">")) | "!=").!
  def combinatorOps[$: P]: P[String] = P("union".! | "intersection".! | "setminus".! | "in".! ~~ spaces | "++".!) // the spaces are there to avaid a very specfic bug introduced by using cuts in compositeOpsExpr
  def cmpOp[$: P]: P[String] = P(">=" | "<=" | ">" | "<").!
  def quantifier[$: P]: P[String] = P("forall" | "exists").!

  // Note regarding assertions:
  // Syntax 1: assertVar is NOT of type State -- forall n: Int :: P(n)
  // Syntax 2: assertVar is of type State -- forall <s1>: State :: P(s1)
  // Syntax 2 is translated to (forall s1: State :: <s1> ==> P)
  // This also means that <s> can only appear at this position (might affect proof var decl?)
 
  def expr[$: P]: P[Expr] = P(Index ~ (assertion | implicationExpr) ~ Index).map { case (oL, exp, oR) => mapExpr(oL, exp, oR) }

  // expressions
  def assertion[$: P]: P[Expr] = P(hyperAssertionErr | hyperAssertion | normalAssertion)
  def normalAssertion[$: P]: P[Expr] = P(quantifier ~~ spaces ~ (normalAssertVarDecl).rep(sep=",", min=1) ~ "::" ~ expr).map(mapNormalAssertion)
  def hyperAssertion[$: P]: P[Expr] = P(Index ~ quantifier ~ ("<"  ~ assertVar ~ ">").rep(sep=",", min=1) ~ "::" ~ expr ~ Index).map { case (oL, quantifier, assertVars, expr, oR) => mapHyperAssertion(oL, quantifier, assertVars, expr, oR) }
  def hyperAssertionErr[$: P]: P[Assertion] = P(quantifier ~ ("<<" ~ assertVar ~ ">>").rep(sep = ",", min = 1) ~ "::" ~ expr).map(mapHyperAssertionErr)

  // this expression should be used when no logical statements are expected
  def implicationExpr[$: P]: P[Expr] = P(Index ~ booleanExpr ~ (impliesOp ~/ expr).? ~ Index).map { case (oL, e, items, oR) => mapImplicationExpr(oL, e, items, oR) }

  def booleanExpr[$: P]: P[Expr] = P(Index ~ booleanEqualityExpr ~ (boolOp1 ~/ booleanExpr).? ~ Index).map { case (oL, e, items, oR) => mapBooleanExpr(oL, e, items, oR) }
  def booleanEqualityExpr[$: P]: P[Expr] = P(Index ~ arithCompExpr ~ (boolOp2 ~/ booleanEqualityExpr).? ~ Index).map { case (oL, e, items, oR) => mapBooleanEqualityExpr(oL, e, items, oR) }
  def arithCompExpr[$: P]: P[Expr] = P(Index ~ arithExpr ~ (cmpOp ~/ arithCompExpr).? ~ Index).map { case (oL, e, items, oR) => mapArithCompExpr(oL, e, items, oR) }
  def arithExpr[$: P]: P[Expr] = P(Index ~ arithTerm ~ (arithOp1 ~/ arithExpr).? ~ Index).map { case (oL, e, items, oR) => mapArithExpr(oL, e, items, oR) }
  def arithTerm[$: P]: P[Expr] = P(Index ~ combinatorOpExpr ~ (arithOp2 ~/ arithTerm).? ~ Index).map { case (oL, e, items, oR) => mapArithTerm(oL, e, items, oR) }

  def combinatorOpExpr[$: P]: P[Expr] = P(Index ~ bracketExpr ~ (combinatorOps ~/ combinatorOpExpr).? ~ Index).map { case (oL, lhs, par, oR) => mapCombinatorOpExpr(oL, lhs, par, oR) }

  def bracketExpr[$: P]: P[Expr] = P(Index ~ basicExpr ~ ("[" ~ (lookupExpr | updateExpr) ~ "]").rep(0) ~ Index).map{
    case (_, base, Nil, _) => base
    case (oL, base, list, oR) =>
      list.foldLeft(base){
        case (prev, (e1, null)) => LookupExpr(prev, e1)
        case (prev, (e1, e2)) => UpdateMapExpr(prev, MapTupleExpr(e1, e2))
      }.setOffsets(oL, oR)
  }

  def lookupExpr[$: P]: P[(Expr, Expr)] = P(implicationExpr).map{ case(expr) => (expr, null)}
  def updateExpr[$: P]: P[(Expr, Expr)] = P(implicationExpr ~ ":=" ~ implicationExpr)

  def basicExpr[$: P]: P[Expr] = P(compositeTypeAssign | lengthExpr | loopIndex | proofVar | boolean | unaryExpr | useHint | identifier | number | "(" ~ expr ~ ")")

  // Basic building components and utils
  def unaryExpr[$: P]: P[UnaryExpr] = P(notExpr | negExpr)
  def notExpr[$: P]: P[UnaryExpr] = P("!" ~ bracketExpr).map(mapNotExpr)
  def negExpr[$: P]: P[UnaryExpr] = P("-" ~ number).map(mapNegExpr)
  def boolean[$: P]: P[BoolLit] = P(boolTrue | boolFalse)
  def boolTrue[$: P]: P[BoolLit] = P("true").!.map(_ => mapBoolTrue())
  def boolFalse[$: P]: P[BoolLit] = P("false").!.map(_ => mapBoolFalse())
  def loopIndex[$: P]: P[LoopIndex] = P("$n").map(_ => mapLoopIndex())
  def number[$: P]: P[Num] = P(CharIn("0-9").rep(1).!.map(_.toInt)).map(mapNumber)
  def useHint[$: P]: P[Expr] = P(Index ~ generalId ~ "(" ~ expr ~ ")" ~ Index).map { case (oL, id, expr, oR) => mapUseHint(oL, id, expr, oR) }

  // Initialisation
  def compositeTypeAssign[$: P]: P[Expr] = P(seqAssignExpr | setAssignExpr | mapAssignExpr)
  def seqAssignExpr[$: P]: P[SeqAssignExpr] = P("Seq[" ~~ notStateTypeName ~~ "]" ~~ "(" ~ expr.rep(sep=",").? ~ ")").map { case (typ, params) => mapSeqAssignExpr(typ, params) }
  def setAssignExpr[$: P]: P[SetAssignExpr] = P("Set[" ~~ notStateTypeName ~~ "]" ~~ "(" ~ expr.rep(sep=",").? ~ ")").map { case (typ, params) => mapSetAssignExpr(typ, params) }
  def mapAssignExpr[$: P]: P[MapAssignExpr] = P("Map[" ~~ notStateTypeName ~~ "," ~ notStateTypeName ~~ "]" ~~ "(" ~ mapTupleExpr.rep(sep=",").? ~ ")").map { case (kTyp, pTyp, params) => mapMapAssignExpr(kTyp, pTyp, params) }
  def mapTupleExpr[$: P]: P[MapTupleExpr] = P(implicationExpr ~ ":=" ~ implicationExpr).map(mapMapTupleExpr)

  def lengthExpr[$: P]: P[LengthExpr] = P("|" ~ implicationExpr ~ "|").map(mapLengthExpr)

  def notStateTypeName[$: P] : P[Type] = P(primitiveTypeName | seqOrSetType | mapType)
  def primitiveTypeName[$: P] : P[Type] = P("Int" | "Bool").!.map(mapPrimitiveTypeName)

  def seqOrSetType[$: P] : P[Type] = P(("Seq" | "Set").! ~~ "[" ~ notStateTypeName ~ "]").map { case (name, t) => mapSeqOrSetType(name, t) }
  def mapType[$: P] : P[Type] = P("Map[" ~ notStateTypeName ~~ "," ~ notStateTypeName ~ "]").map { case (t1, t2) => mapMapType(t1, t2) }
  def spaces[$: P]: P[Unit] = P(CharIn(" \r\n\t").rep(1))
  def generalId[$: P]: P[String] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!
}