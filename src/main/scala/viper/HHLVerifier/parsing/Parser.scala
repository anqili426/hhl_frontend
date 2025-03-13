package viper.HHLVerifier.parsing

import fastparse.JavaWhitespace._
import fastparse._
import viper.HHLVerifier.parsing.Mappings._
import viper.HHLVerifier.typing.Type
import viper.HHLVerifier._

/** The Parser object
 *
 * This class contains all parsing rules written in fastparse. Calling parse on program will create an AST or
 * result in a parsing error.
 *
 * Concrete Mappings can be found in [[viper.HHLVerifier.parsing.Mappings]].
 */
object Parser {
  /** The program parser: Parses an entire HHLProgram or will throw a `Logger` object with a type error. */
  def program[$: P]: P[HHLProgram] = P(Start ~ method.rep ~ End).map(mapProgram)

  /** Method parser: Parses and individual method with its name, preconditions, postconditions, parameters and return values. */
  def method[$: P]: P[Method] = P(Index ~ "method" ~~ spaces ~~ methodName ~ Index ~ "(" ~ methodVarDecl.rep(sep=",") ~ ")"  ~ ("returns" ~ "(" ~ methodVarDecl.rep(sep=",") ~ ")").? ~ precondition.rep ~ postcondition.rep  ~"{" ~ stmts ~ "}").map(mapMethod)
  def precondition[$: P]: P[Expr] = P("requires" ~~ spaces ~ expr)
  def postcondition[$: P]: P[Expr] = P("ensures" ~~ spaces ~ expr)
  def methodName[$: P]: P[String] = P(CharIn("a-zA-Z_") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.log
  def methodVarDecl[$: P]: P[Id] = P(progVar ~ ":" ~ progTypes).map(mapMethodVarDecl)

  /** General identifier object: Refers to all entries of the symbol table except methods. */
  def identifier[$: P]: P[Expr] = P(Index ~ (progVar | assertVar | proofVar) ~ Index).map { case (oL, id, oR) => mapIdentifier(oL, id, oR) }
  
  /** Program variables
   *
   * Program variables to refer to all variables which have assigned values in the program code.
   * Use case: {{{var num: Int }}} */
  def progVar[$: P]: P[Id] = generalId.map(name => Id(name)).log
  def varDecl[$: P] : P[PVarDecl] = P("var" ~ progVar ~ ":" ~ progTypes).map(mapVarDecl)

  /** Assert variables
   *
   * Assert variables are used in assertions to describe states. They can be used only in assertions!
   * Use case: {{{hyperAssert forall <_s> :: _s[num] == 2}}} */
  def assertVar[$: P]: P[AssertVar] = P("_" ~~ CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(name => AssertVar(name))
  def normalAssertVarDecl[$: P] : P[AssertVarDecl] = P(assertVar ~ ":" ~ progTypes).map(mapNormalAssertVarDecl)

  /** Proof variables
   *
   * TODO: Insert description.
   * Declared with let ..., start with $, used in statements. */
  def proofVar[$: P]: P[ProofVar] = P("$" ~~ CharIn("a-mo-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(ProofVar)
  def proofVarDecl[$: P]: P[ProofVarDecl] = P(stateProofVarDeclErr | stateProofVarDecl | normalProofVarDecl)
  def normalProofVarDecl[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ proofVar ~ ":" ~ progTypes ~ "::" ~ expr).map(mapNormalProofVarDecl)
  def stateProofVarDecl[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ "<" ~ proofVar ~ ">" ~ ("::" ~ expr).?).map(mapStateProofVarDecl)
  def stateProofVarDeclErr[$: P]: P[ProofVarDecl] = P("let" ~~ spaces ~ "<<" ~ proofVar ~ ">>" ~ ("::" ~ expr).?).map(mapStateProofVarDeclErr)

  /** Statements
   *
   * Statements are the basic building blocks of every Hypra program. They are used to perform actions which change
   * program states. */
  def stmts[$: P] : P[CompositeStmt] = P(stmt.rep).map(CompositeStmt)
  def stmt[$: P] : P[Stmt] = P(Index ~ (
    varDecl | proofVarDecl |
    assign | multiAssign |
    ifElse | whileLoop |
    assume | assert | havoc | frame | hyperAssume | hyperAssert | useHintStmt
  ) ~ Index).map { case (oL, stmt, oR) => mapStmt(oL, stmt, oR) }
  /** MultiAssign Statement
   *
   * Assigns the return values of a function call to multiple variables.
   * Use case: {{{
   *   var a: Int, b: Int, c: Int
   *   a, b, c := assignThreeValues()
   * }}}*/
  def multiAssign[$: P]: P[MultiAssignStmt] = P(progVar.rep(sep=",", min=1) ~ ":=" ~ methodCall).map(mapMultiAssign).log
  /** Assign Statement
   *
   * Assigns the result of an expression to a program variable.
   * Use case: {{{
   *   var a: Int
   *   a := (2 * 3) + 4
   * }}}*/
  def assign[$: P] : P[AssignStmt] = P(progVar ~ ":=" ~ implicationExpr).map(mapAssign).log
  /** Havoc Statement
   *
   * Randomly assigns a value to a program variable.
   * Use case: {{{
   *   var a: Int
   *   havoc a
   * }}}*/
  def havoc[$: P] : P[HavocStmt] = P("havoc" ~~ spaces ~ progVar ~ hintDecl.?).map { case (v, hintDecl) => mapHavoc(v, hintDecl) }
  /** Assume Statement: Assumes an expression on the viper level. */
  def assume[$: P] : P[AssumeStmt] = P("assume" ~~ spaces ~ (normalAssertion | implicationExpr)).map(mapAssume)
  /** Assert Statement: Asserts an expression on the viper level. */
  def assert[$: P] : P[AssertStmt] = P("assert" ~~ spaces ~ (normalAssertion | implicationExpr)).map(mapAssert)
  /** Hyper Assume Statement: Assumes a hyper assertions. */
  def hyperAssume[$: P]: P[HyperAssumeStmt] = P("hyperAssume" ~~ spaces ~ expr).map(mapHyperAssume)
  /** Hyper Assert Statement: Asserts a hyper assertions. */
  def hyperAssert[$: P]: P[HyperAssertStmt] = P("hyperAssert" ~~ spaces ~ expr).map(mapHyperAssert)
  def declareStmt[$: P]: P[DeclareStmt] = P("declare" ~~ spaces ~ blockId ~ "{" ~ stmts ~ "}").map(mapDeclareStmt)
  def reuseStmt[$: P]: P[ReuseStmt] = P("reuse" ~~ spaces ~ blockId).map(mapReuseStmt)
  def stmtInIf[$: P]: P[Stmt] = P(stmt | declareStmt)
  def stmtsInIf[$: P]: P[CompositeStmt] = P(stmtInIf.rep).map(CompositeStmt)
  def stmtInElse[$: P]: P[Stmt] = P(stmt | reuseStmt)
  def stmtsInElse[$: P]: P[CompositeStmt] = P(stmtInElse.rep).map(CompositeStmt)
  /** IfElse Statement: Declares an if-else statement. The else block is optional. */
  def ifElse[$: P] : P[IfElseStmt] = P("if" ~ "(" ~ implicationExpr ~ ")" ~ "{" ~ stmtsInIf ~ "}" ~ ("else" ~ "{" ~ stmtsInElse ~ "}").?).map { case (e, s1, s2) => mapIfElse(e, s1, s2) }
  /** WhileLoop Statement: Declares a while loop. */
  def whileLoop[$: P] : P[WhileLoopStmt] = P("while" ~~ spaces ~ ("syncRule" | "forAllExistsRule" | "existsRule" | "syncTotRule" | "desugaredRule").?.! ~ "(" ~ implicationExpr ~ ")"  ~ loopInv.rep ~ ("decreases" ~ arithExpr).? ~ "{" ~ stmts ~ "}").map(mapWhileLoop)
  /** Frame Statement: Declare a frame. */
  def frame[$: P]: P[FrameStmt] = P("frame" ~~ spaces ~ expr ~ "{" ~ stmts ~ "}").map(mapFrame)
  /** UseHint Statement: Use a hint declare trigger for havoc statments. */
  def useHintStmt[$: P]: P[UseHintStmt] = P("use" ~~ spaces ~ useHint).map(mapUseHintStmt)

  // Utils for statements
  /** LoopInvariant: Declares an invariant in a while loop. */
  def loopInv[$: P]: P[(Option[HintDecl], Expr)] = P(hintDecl.? ~ "invariant" ~~ spaces ~ expr)
  def blockId[$: P]: P[Id] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!.map(mapBlockId)
  /** HintDeclaration: Declare a hint related to a havoc statement. */
  def hintDecl[$: P]: P[HintDecl] = P("{" ~ generalId ~ "}").map(HintDecl)
  def useHint[$: P]: P[Expr] = P(Index ~ generalId ~ "(" ~ expr ~ ")" ~ Index).map { case (oL, id, expr, oR) => mapUseHint(oL, id, expr, oR) }

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

  /** Expression: Parent for all expressions and assertions.
   *
   * This includes every kind of expression and assertion which can be written in Hyper Hoare Logic. */
  def expr[$: P]: P[Expr] = P(Index ~ (assertion | implicationExpr) ~ Index).map { case (oL, exp, oR) => mapExpr(oL, exp, oR) }

  // expressions
  /** Assertion: Parent for all assertions */
  def assertion[$: P]: P[Expr] = P(hyperAssertionErr | hyperAssertion | normalAssertion)
  /** Normal Assertions: Assertions over program and proof variables, without states or hyper hoare logic. */
  def normalAssertion[$: P]: P[Expr] = P(quantifier ~~ spaces ~ (normalAssertVarDecl).rep(sep=",", min=1) ~ "::" ~ expr).map(mapNormalAssertion)
  /** Hyper Assertion: Assertions over sets of states in Hyper Hoare Logic. */
  def hyperAssertion[$: P]: P[Expr] = P(Index ~ quantifier ~ ("<"  ~ assertVar ~ ">").rep(sep=",", min=1) ~ "::" ~ expr ~ Index).map { case (oL, quantifier, assertVars, expr, oR) => mapHyperAssertion(oL, quantifier, assertVars, expr, oR) }
  /** Hyper Assertion: Assertions over sets of *error* states in Hyper Hoare Logic. */
  def hyperAssertionErr[$: P]: P[Assertion] = P(quantifier ~ ("<<" ~ assertVar ~ ">>").rep(sep = ",", min = 1) ~ "::" ~ expr).map(mapHyperAssertionErr)

  // this expression should be used when no logical statements are expected
  /** Implication Expression: All kinds of expression which don't include assertions */
  def implicationExpr[$: P]: P[Expr] = P(Index ~ booleanExpr ~ (impliesOp ~/ expr).? ~ Index).map { case (oL, e, items, oR) => mapImplicationExpr(oL, e, items, oR) }
  /** Boolean Expression: Expressions containing || or &&. */
  def booleanExpr[$: P]: P[Expr] = P(Index ~ booleanEqualityExpr ~ (boolOp1 ~/ booleanExpr).? ~ Index).map { case (oL, e, items, oR) => mapBooleanExpr(oL, e, items, oR) }
  /** Boolean Equality Expression: Expressions containing ==. */
  def booleanEqualityExpr[$: P]: P[Expr] = P(Index ~ arithCompExpr ~ (boolOp2 ~/ booleanEqualityExpr).? ~ Index).map { case (oL, e, items, oR) => mapBooleanEqualityExpr(oL, e, items, oR) }
  /** Arithmetic Comparison Expression: Expressions containing >=, <=, ==, != */
  def arithCompExpr[$: P]: P[Expr] = P(Index ~ arithExpr ~ (cmpOp ~/ arithCompExpr).? ~ Index).map { case (oL, e, items, oR) => mapArithCompExpr(oL, e, items, oR) }
  /** Arithmetic Expression: Expressions containing +, - */
  def arithExpr[$: P]: P[Expr] = P(Index ~ arithTermExpr ~ (arithOp1 ~/ arithExpr).? ~ Index).map { case (oL, e, items, oR) => mapArithExpr(oL, e, items, oR) }
  /** Arithmetic Term Expression: Expressions containing /, *, % */
  def arithTermExpr[$: P]: P[Expr] = P(Index ~ combinatorOpExpr ~ (arithOp2 ~/ arithTermExpr).? ~ Index).map { case (oL, e, items, oR) => mapArithTerm(oL, e, items, oR) }
  /** Combinator Operation Expression: Expressions containing operations relating composite types like ++, union, intersection, ... */
  def combinatorOpExpr[$: P]: P[Expr] = P(Index ~ bracketExpr ~ (combinatorOps ~/ combinatorOpExpr).? ~ Index).map { case (oL, lhs, par, oR) => mapCombinatorOpExpr(oL, lhs, par, oR) }
  /** Bracket Expression: Expression containing lookup operation to states or composite types OR map updates. */
  def bracketExpr[$: P]: P[Expr] = P(Index ~ basicExpr ~ ("[" ~ (lookupExpr | updateExpr) ~ "]").rep(0) ~ Index).map{
    case (_, base, Nil, _) => base
    case (oL, base, list, oR) =>
      list.foldLeft(base){
        case (prev, (e1, null)) => LookupExpr(prev, e1)
        case (prev, (e1, e2)) => UpdateMapExpr(prev, MapTupleExpr(e1, e2))
      }.setOffsets(oL, oR)
  }
  /** Lookup Expression: Accessing values from a base object. */
  def lookupExpr[$: P]: P[(Expr, Expr)] = P(implicationExpr).map{ case(expr) => (expr, null)}
  /** UpdateExpr: Updating a value for a key in a map */
  def updateExpr[$: P]: P[(Expr, Expr)] = P(implicationExpr ~ ":=" ~ implicationExpr)

  /** Basic Expression: Fundamental expression, hanlding all basic cases. */
  def basicExpr[$: P]: P[Expr] = P(compositeTypeAssign | lengthExpr | loopIndex | proofVar | boolean | unaryExpr | methodCall | identifier | number  | "(" ~ expr ~ ")")

  // Basic building components and utils
  def unaryExpr[$: P]: P[UnaryExpr] = P(notExpr | negExpr)
  def notExpr[$: P]: P[UnaryExpr] = P("!" ~ bracketExpr).map(mapNotExpr)
  def negExpr[$: P]: P[UnaryExpr] = P("-" ~ number).map(mapNegExpr)
  def boolean[$: P]: P[BoolLit] = P(boolTrue | boolFalse)
  def boolTrue[$: P]: P[BoolLit] = P("true").!.map(_ => mapBoolTrue())
  def boolFalse[$: P]: P[BoolLit] = P("false").!.map(_ => mapBoolFalse())
  def loopIndex[$: P]: P[LoopIndex] = P("$n").map(_ => mapLoopIndex())
  def number[$: P]: P[Num] = P(CharIn("0-9").rep(1).!.map(_.toInt)).map(mapNumber)
  def methodCall[$: P]: P[MethodCallExpr] = P(methodName ~ "(" ~ progVar.rep(sep=",", min=0) ~")").map{
    case (name, vars) => MethodCallExpr(name, vars)
  }.log

  // Initialisation
  /** Composite Type Assign: Parent for all composite type assignments. */
  def compositeTypeAssign[$: P]: P[Expr] = P(seqAssignExpr | setAssignExpr | mapAssignExpr)
  /** Sequence Assign Expression: Creates a new Sequence object like Seq[Int](v1, v2, v3) */
  def seqAssignExpr[$: P]: P[SeqAssignExpr] = P("Seq[" ~~ progTypes ~~ "]" ~~ "(" ~ expr.rep(sep=",").? ~ ")").map { case (typ, params) => mapSeqAssignExpr(typ, params) }
  /** SetAssign Expression: Creates a new Set object like Set[Int](v1, v2, v3) */
  def setAssignExpr[$: P]: P[SetAssignExpr] = P("Set[" ~~ progTypes ~~ "]" ~~ "(" ~ expr.rep(sep=",").? ~ ")").map { case (typ, params) => mapSetAssignExpr(typ, params) }
  /** Map Assign Expression: Creates a new Map object like Map[Int](k1 := v1, k2 := v2, k3 := v3) */
  def mapAssignExpr[$: P]: P[MapAssignExpr] = P("Map[" ~~ progTypes ~~ "," ~ progTypes ~~ "]" ~~ "(" ~ mapTupleExpr.rep(sep=",").? ~ ")").map { case (kTyp, pTyp, params) => mapMapAssignExpr(kTyp, pTyp, params) }
  def mapTupleExpr[$: P]: P[MapTupleExpr] = P(implicationExpr ~ ":=" ~ implicationExpr).map(mapMapTupleExpr)

  /** Length Expression: Calculates the size of a compsoite object. */
  def lengthExpr[$: P]: P[LengthExpr] = P("|" ~ implicationExpr ~ "|").map(mapLengthExpr)

  // Typing
  /** Programing Types: Parent class for all types which are used by program variables. */
  def progTypes[$: P] : P[Type] = P(primitiveTypes | seqOrSetType | mapType)
  /** Primitive Types: Parent for all primitive types. */
  def primitiveTypes[$: P] : P[Type] = P("Int" | "Bool").!.map(mapPrimitiveTypeName)

  def seqOrSetType[$: P] : P[Type] = P(("Seq" | "Set").! ~~ "[" ~ progTypes ~ "]").map { case (name, t) => mapSeqOrSetType(name, t) }
  def mapType[$: P] : P[Type] = P("Map[" ~ progTypes ~~ "," ~ progTypes ~ "]").map { case (t1, t2) => mapMapType(t1, t2) }

  // Utils
  /** Spaces: Consumes at least one space, newline or tab. */
  def spaces[$: P]: P[Unit] = P(CharIn(" \r\n\t").rep(1))
  /** General Id: Basic building block for ids. */
  def generalId[$: P]: P[String] = P(CharIn("a-zA-Z") ~~ CharsWhileIn("a-zA-Z0-9_", 0)).!
}