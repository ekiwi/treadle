// See LICENSE for license details.

package treadle.symbolic

import scala.collection.mutable
import net.sf.javabdd.{BDD, JFactory}
import uclid.{Hashable, smt}
import firrtl.ir

class YicesInterface extends smt.SMTLIB2Interface(List("yices-smt2", "--incremental")) {
  writeCommand("(set-logic QF_AUFBV)")
}

class Z3ProcessInterface extends smt.SMTLIB2Interface(List("z3", "-in"))

//scalastyle:off magic.number
class SymbolicContext {
  val solver : smt.Context = new YicesInterface()

  private val bdds = JFactory.init(100, 100)
  private var bddVarCount = 0
  private val smtToBddCache: mutable.HashMap[Hashable, BDD] = new mutable.HashMap()
  private val bddLiteralToSmt: mutable.HashMap[Int, smt.Expr] = new mutable.HashMap()


  def smtToBDD(expr: smt.Expr) : BDD = {
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
      val cond = bddLiteralToSmt(bdd.`var`())
      val tru = bddToSmt(bdd.high())
      val fal = bddToSmt(bdd.low())
      smt.OperatorApplication(smt.ITEOp, List(cond, tru, fal))
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
          case _=> throw new RuntimeException(s"unexpected type for expression $expr")
        }
      case None => throw new RuntimeException(s"unexpected solver result `$smtResult` for expression $expr")
    }
  }
}

case class SymbolicValue(name: String, cycle: Int, tpe: ir.Type, signal: String, sym: smt.Expr)
