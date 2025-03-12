package viper.HHLVerifier.parser

import viper.HHLVerifier.generation.Generator
import viper.HHLVerifier.{AssertStmt, AssertVar, AssertVarDecl, Assertion, AssignStmt, AssumeStmt, BinaryExpr, BoolLit, BoolType, CombExpr, CompositeStmt, DeclareStmt, Expr, FrameStmt, HHLProgram, HavocStmt, Hint, HintDecl, HyperAssertStmt, HyperAssumeStmt, Id, IfElseStmt, ImpliesExpr, IntType, LengthExpr, LookupExpr, LoopIndex, MapAssignExpr, MapTupleExpr, MapType, Method, MethodCallExpr, MethodCallStmt, MultiAssignStmt, Num, PVarDecl, ProofVar, ProofVarDecl, ReuseStmt, SeqAssignExpr, SeqType, SetAssignExpr, SetType, StateExistsExpr, StateType, Stmt, Type, TypeInstance, UnaryExpr, UnknownException, UpdateMapExpr, UseHintStmt, WhileLoopStmt}

// This file contains all the actual mappings from parsing rules to object. As those are not very important and
// mostly tedious work, they were shifted into this file.
// To understand this, look at the parsing rule, and then at the mapping rule.

object Mappings {
  def mapProgram(methods: Seq[Method]): HHLProgram = methods match {
    case Nil => HHLProgram(Seq.empty)
    case methods => HHLProgram(methods)
  }

  def mapMethod(items: (Int, String, Int, Seq[Id], Option[Seq[Id]], Seq[Expr], Seq[Expr], CompositeStmt)): Method = {
    val args = if (items._4 != Nil) items._4 else Seq.empty
    val res = if (items._5 != None) items._5.get else Seq.empty
    val pre = if (items._6 != Nil) items._6 else Seq.empty
    val post = if (items._7 != Nil) items._7 else Seq.empty
    Method(items._2, args, res, pre, post, items._8, items._1, items._3)
  }

  def mapMethodVarDecl(items: (Id, Type)): Id = {
    items._1.typ = items._2
    items._1
  }

  def mapIdentifier(oL: Int, id: Expr, oR: Int): Expr = id.setOffsets(oL, oR)

  def mapBlockId(name: String): Id = {
      val blockId = Id(name)
      blockId.typ = TypeInstance.stmtBlockType
      blockId
  }

  def mapNormalProofVarDecl(items: (ProofVar, Type, Expr)): ProofVarDecl = {
    items._1.typ = items._2
    ProofVarDecl(items._1, items._3)
  }

  def mapStateProofVarDecl(items: (ProofVar, Option[Expr])): ProofVarDecl = {
    items._1.typ = StateType()
    val stateExistsExpr = StateExistsExpr(items._1, false)
    val body = if (items._2.isEmpty) stateExistsExpr else BinaryExpr(stateExistsExpr, "&&", items._2.get)
    ProofVarDecl(items._1, body)
  }

  def mapStateProofVarDeclErr(items: (ProofVar, Option[Expr])): ProofVarDecl = {
    items._1.typ = StateType()
    val stateExistsExpr = StateExistsExpr(items._1, true)
    val body = if (items._2.isEmpty) stateExistsExpr else BinaryExpr(stateExistsExpr, "&&", items._2.get)
    ProofVarDecl(items._1, body)
  }

  def mapVarDecl(items: (Id, Type)): PVarDecl = PVarDecl(items._1, items._2)

  def mapStmt(oL: Int, stmt: Stmt, oR: Int): Stmt = stmt.setOffsets(oL, oR)
  def mapMultiAssign(items: (Seq[Id], MethodCallExpr)): MultiAssignStmt = MultiAssignStmt(items._1, items._2)
  def mapAssign(e: (Id, Expr)): AssignStmt = AssignStmt(e._1, e._2)
  def mapHavoc(v: Id, hintDecl: Option[HintDecl]): HavocStmt = hintDecl match {
    case None => HavocStmt(v, Option.empty)
    case Some(hintDecl) => HavocStmt(v, Some(hintDecl))
  }
  def mapAssume(e: Expr): AssumeStmt = AssumeStmt(e)
  def mapAssert(e: Expr): AssertStmt = AssertStmt(e)
  def mapHyperAssume(e: Expr): HyperAssumeStmt = HyperAssumeStmt(e)
  def mapHyperAssert(e: Expr): HyperAssertStmt = HyperAssertStmt(e)
  def mapDeclareStmt(items: (Id, CompositeStmt)): DeclareStmt = DeclareStmt(items._1, items._2)
  def mapReuseStmt(e: Id): ReuseStmt = ReuseStmt(e)
  def mapIfElse(e: Expr, s1: CompositeStmt, s2: Option[CompositeStmt]): IfElseStmt = IfElseStmt(e, s1, s2.getOrElse(CompositeStmt(Seq())))
  def mapWhileLoop(items: (String, Expr, Seq[(Option[HintDecl], Expr)], Option[Expr], CompositeStmt)): WhileLoopStmt = {
    val rule = if (items._1 == "" && !Generator.autoSelectRules) throw UnknownException("Each while loop must be specified with exactly one rule unless auto-selection of rules is turned on. ")
    else if (items._1 == "") "unspecified" else items._1
    val cond = items._2
    val invs = if (items._3 == Nil) Seq.empty else items._3
    val decr = if (items._4.isEmpty) Option.empty else items._4
    val body = items._5
    if (rule == "syncTotRule" && decr.isEmpty) throw UnknownException("Users must provide a decreases clause to use the syncTot Rule")
    WhileLoopStmt(cond, body, invs, decr, rule)
  }
  def mapFrame(items: (Expr, CompositeStmt)): FrameStmt = FrameStmt(items._1, items._2)
  def mapUseHintStmt(e: Expr): UseHintStmt = UseHintStmt(e)
  def mapMethodCallStmt(items: (String, Seq[Id])): MethodCallStmt = MethodCallStmt(items._1, items._2)

  def mapNormalAssertVarDecl(items: (AssertVar, Type)): AssertVarDecl = AssertVarDecl(items._1, items._2)

  def mapNormalAssertion(items: (String, Seq[AssertVarDecl], Expr)): Assertion = Assertion(items._1, items._2, items._3)

  def mapHyperAssertion(oL: Int, quantifier: String, assertVars: Seq[AssertVar], expr: Expr, oR: Int): Expr = {
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

  def mapHyperAssertionErr(items: (String, Seq[AssertVar], Expr)): Assertion = {
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

  def mapExpr(oL: Int, exp: Expr, oR: Int): Expr = exp.setOffsets(oL, oR)

  def mapImplicationExpr(oL: Int, e: Expr, items: Option[(String, Expr)], oR: Int): Expr = items match {
    case None => e
    case Some((_, expr)) => ImpliesExpr(e, expr).setOffsets(oL, oR)
  }

  def mapBooleanExpr(oL: Int, e: Expr, items: Option[(String, Expr)], oR: Int): Expr = items match {
    case None => e
    case Some((op, expr)) => BinaryExpr(e, op, expr).setOffsets(oL, oR)
  }

  def mapBooleanEqualityExpr(oL: Int, e: Expr, items: Option[(String, Expr)], oR: Int): Expr = items match {
    case None => e
    case Some((op, expr)) => BinaryExpr(e, op, expr).setOffsets(oL, oR)
  }

  def mapArithCompExpr(oL: Int, e: Expr, items: Option[(String, Expr)], oR: Int): Expr = items match {
    case None => e
    case Some((op, expr)) => BinaryExpr(e, op, expr).setOffsets(oL, oR)
  }

  def mapArithExpr(oL: Int, e: Expr, items: Option[(String, Expr)], oR: Int): Expr = items match {
    case None => e
    case Some((op, expr)) => BinaryExpr(e, op, expr).setOffsets(oL, oR)
  }

  def mapArithTerm(oL: Int, e: Expr, items: Option[(String, Expr)], oR: Int): Expr = items match {
    case None => e
    case Some((op, expr)) => BinaryExpr(e, op, expr).setOffsets(oL, oR)
  }

  def mapCombinatorOpExpr(oL: Int, lhs: Expr, par: Option[(String, Expr)], oR: Int): Expr = par match {
    case None => lhs
    case Some((op, rhs)) => CombExpr(lhs, rhs, op).setOffsets(oL, oR)
  }

  def mapMapUpdate(oL: Int, base: Expr, items: Option[(Expr, Expr)], oR: Int): Expr = items match {
    case None => base
    case Some((k, v)) => UpdateMapExpr(base, MapTupleExpr(k, v)).setOffsets(oL, oR)
  }

  def mapAccessValExpr(oL: Int, lhs: Expr, l: Option[Expr], oR: Int): Expr = l match {
    case None => lhs
    case Some(expr) => LookupExpr(lhs, expr).setOffsets(oL, oR)
  }

  def mapNotExpr(e: Expr): UnaryExpr = UnaryExpr("!", e)

  def mapNegExpr(e: Num): UnaryExpr = UnaryExpr("-", e)

  def mapBoolTrue(): BoolLit = BoolLit(true)

  def mapBoolFalse(): BoolLit = BoolLit(false)

  def mapLoopIndex(): LoopIndex = LoopIndex()

  def mapNumber(value: Int): Num = Num(value)

  def mapUseHint(oL: Int, id: String, expr: Expr, oR: Int): Hint = Hint(id, expr).setOffsets(oL, oR).asInstanceOf[Hint]

  def mapSeqAssignExpr(typ: Type, params: Option[Seq[Expr]]): SeqAssignExpr = {
    val exp = SeqAssignExpr(params.getOrElse(Seq.empty))
    exp.typ = SeqType(typ)
    exp
  }

  def mapSetAssignExpr(typ: Type, params: Option[Seq[Expr]]): SetAssignExpr = {
    val exp = SetAssignExpr(params.getOrElse(Seq.empty))
    exp.typ = SetType(typ)
    exp
  }

  def mapMapAssignExpr(kTyp: Type, pTyp: Type, params: Option[Seq[MapTupleExpr]]): MapAssignExpr = {
    val exp = MapAssignExpr(params.getOrElse(Seq.empty))
    exp.typ = MapType(kTyp, pTyp)
    exp
  }

  def mapMapTupleExpr(items: (Expr, Expr)): MapTupleExpr = MapTupleExpr(items._1, items._2)

  def mapLengthExpr(expr: Expr): LengthExpr = LengthExpr(expr)

  def mapPrimitiveTypeName(name: String): Type = name match {
    case "Int" => IntType()
    case "Bool" => BoolType()
  }

  def mapSeqOrSetType(name: String, t: Type): Type = name match {
    case "Seq" => SeqType(t)
    case "Set" => SetType(t)
    case _ => throw UnknownException("Critical error occurred while parsing Seq/Set type declarations")
  }

  def mapMapType(t1: Type, t2: Type): MapType = MapType(t1, t2)
}
