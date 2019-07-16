// See LICENSE for license details.

package treadle.symbolic

import org.scalatest.{Matchers, FreeSpec}
import uclid.smt._

class YicesInterface extends SMTLIB2Interface(List("yices-smt2", "--incremental")) {
  writeCommand("(set-logic QF_AUFBV)")
}

class Z3ProcessInterface extends SMTLIB2Interface(List("z3", "-in"))


class Uclid5SMTSpec extends FreeSpec with Matchers {
  //scalastyle:off magic.number
  val solver = new YicesInterface()
  private def bv_t(w: Int) = BitVectorType(w)
  private def op(op: Operator, operands: Expr*) = {
    OperatorApplication(op, operands.toList)
  }

  "check equivalence of signed and unsigned sum" in {
    val x = Symbol("x", bv_t(32))
    val y = Symbol("y", bv_t(32))
    val carry_in = Symbol("carry_in", bv_t(1))
    val unsigned_sum = op(BVAddOp(33), op(BVAddOp(33), op(BVZeroExtOp(33, 1), x), op(BVZeroExtOp(33, 1), y)), op(BVZeroExtOp(33, 32), carry_in))
    val signed_sum =   op(BVAddOp(33), op(BVAddOp(33), op(BVSignExtOp(33, 1), x), op(BVSignExtOp(33, 1), y)), op(BVZeroExtOp(33, 32), carry_in))

    val res32_equal = op(EqualityOp, op(BVExtractOp(31, 0), unsigned_sum), op(BVExtractOp(31, 0), signed_sum))


    solver.push()
    solver.assert(op(NegationOp, res32_equal))
    val res = solver.check()
    solver.pop()
    res.isFalse should be (true)
  }

}
