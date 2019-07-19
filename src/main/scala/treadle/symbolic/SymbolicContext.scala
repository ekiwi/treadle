// See LICENSE for license details.

package treadle.symbolic

import scala.collection.mutable
import net.sf.javabdd.{BDD, JFactory, BDDFactory}
import uclid.{Hashable, smt}
import firrtl.ir

class YicesInterface extends smt.SMTLIB2Interface(List("yices-smt2", "--incremental")) {
  writeCommand("(set-logic QF_AUFBV)")

  override def getModel() : Option[smt.Model] = {
    uclid.Utils.assert(solverProcess.isAlive(), "Solver process is not alive! Cannot retrieve model.")
    writeCommand("(get-model)")
    readResponse() match {
      case Some(strModel) =>
        Some(new smt.SMTLIB2Model(strModel.stripLineEnd))
      case None =>
        throw new uclid.Utils.AssertionError("Unexpected EOF result from SMT solver.")
    }
  }
}

class Z3ProcessInterface extends smt.SMTLIB2Interface(List("z3", "-in"))

//scalastyle:off magic.number cyclomatic.complexity
class SymbolicContext(
   // MultiSE 3.2: without coalescing we get an algorithm that behaves essentially like conventional DSE
   val DoNotCoalesce : Boolean = false,
   // This will slow down symbolic execution significantly, only enable for debugging
   val CrosscheckSmtWithConcrete : Boolean = false,
   // SMT solver to use
   val solver : smt.Context = new YicesInterface(),
   // BDD implementation
   private val bdds : BDDFactory = JFactory.init(100, 100)
 ) {


  private var bddVarCount = 0
  private val smtToBddCache: mutable.HashMap[Hashable, BDD] = new mutable.HashMap()
  private val bddLiteralToSmt: mutable.HashMap[Int, smt.Expr] = new mutable.HashMap()

  val tru : BDD = bdds.one()
  val fals : BDD = bdds.zero()

  // register smt expressions for literal zero and one
  smtToBddCache(smt.BooleanLit(true)) = tru
  smtToBddCache(smt.BooleanLit(false)) = fals

  def smtToBdd(expr: smt.Expr) : BDD = {
    assert(expr.typ.isBool, s"can only convert boolean expressions to BDD, but `$expr` is of type ${expr.typ}")
    if(!smtToBddCache.contains(expr)) {
      // TODO: if expr is a OperatorApplication w/ a boolean operator, we could add more info to the BDD
      if(bdds.varNum() <= bddVarCount) {
        bdds.setVarNum(bddVarCount + 1)
      }
      smtToBddCache(expr) = bdds.ithVar(bddVarCount)
      bddLiteralToSmt(bddVarCount) = expr
      bddVarCount += 1
    }
    smtToBddCache(expr)
  }

  def bddToSmt(bdd: BDD) : smt.Expr = {
    if(bdd.isOne) { smt.BooleanLit(true) }
    else if(bdd.isZero) { smt.BooleanLit(false) }
    else {
      // all cases verified with sympy:
      // simplify_logic(ITE(c, 1, 0)) = c
      // simplify_logic(ITE(c, 0, 1)) = ~c
      // simplify_logic(ITE(c, 1, b)) = b | c
      // simplify_logic(ITE(c, 0, b)) = b & ~c
      // simplify_logic(ITE(c, b, 1)) = b | ~c
      // simplify_logic(ITE(c, b, 0)) = b & c
      val high_is_one  = bdd.high().isOne
      val high_is_zero = bdd.high().isZero
      val low_is_one   = bdd.low().isOne
      val low_is_zero  = bdd.low().isZero
      val is_var = high_is_one && low_is_zero
      val is_neg_var = high_is_zero && low_is_one
      val is_or_var = high_is_one
      val is_and_neg_var = high_is_zero
      val is_or_neg_var = low_is_one
      val is_and_var = low_is_zero

      val cond = bddLiteralToSmt(bdd.`var`())
      lazy val neg_cond = smt.OperatorApplication(smt.NegationOp, List(cond))

      if(is_var) { cond }
      else if(is_neg_var) { neg_cond }
      else if(is_or_var || is_and_neg_var) {
        val b = bddToSmt(bdd.low())
        if(is_or_var) { smt.OperatorApplication(smt.DisjunctionOp, List(cond, b)) }
        else          { smt.OperatorApplication(smt.ConjunctionOp, List(neg_cond, b)) }
      }
      else if(is_or_neg_var || is_and_var) {
        val b = bddToSmt(bdd.high())
        if(is_or_neg_var) { smt.OperatorApplication(smt.DisjunctionOp, List(neg_cond, b)) }
        else              { smt.OperatorApplication(smt.ConjunctionOp, List(cond, b)) }
      }
      else {
        val tru = bddToSmt(bdd.high())
        val fal = bddToSmt(bdd.low())
        val args = cond match {
          case smt.OperatorApplication(smt.NegationOp, List(n_cond)) => List(n_cond, fal, tru)
          case _ => List(cond, tru, fal)
        }
        smt.OperatorApplication(smt.ITEOp, args)
      }
    }
  }

  // inspired by the ExpressionAnalyzer in Uclid5
  def eval(expr: smt.Expr, ensureUniqueness: Boolean = false) : BigInt = {
    assert(expr.typ.isBitVector || expr.typ.isBool, "currently, only BV and bool are supported")
    if(ensureUniqueness) {
      val expr_copy = smt.Converter.renameSymbols(expr, (s, t) => s + "_copy")
      // we want to prove that for all possible inputs to the expression, the value will be the same
      solver.push()
      solver.assert(smt.OperatorApplication(smt.InequalityOp, List(expr, expr_copy)))
      val smtResult = solver.check()
      solver.pop()
      val isConst = smtResult.isFalse
      assert(isConst, s"expression $expr does not have a unique value!")
    }
    val lit = smt.Symbol("$value_123", expr.typ)
    solver.push()
    solver.assert(smt.OperatorApplication(smt.EqualityOp, List(expr, lit)))
    val smtResult = solver.check()
    solver.pop()
    smtResult.model match {
      case Some(m) =>
        m.evaluate(lit) match {
          case smt.BooleanLit(value) => if(value) { BigInt(1) } else { BigInt(0) }
          case smt.BitVectorLit(value, _) => value
          case smt.Symbol(id, _) => id match {
            case "true" => BigInt(1)
            case "false" => BigInt(0)
            case o => throw new RuntimeException(s"unexpeced symbol $o for expression $expr")
          }
          case l => throw new RuntimeException(s"unexpected type for expression $expr => $l")
        }
      case None => throw new RuntimeException(s"unexpected solver result `$smtResult` for expression $expr")
    }
  }
}

case class SymbolicValue(name: String, cycle: Int, tpe: ir.Type, signal: String, sym: smt.Expr)
