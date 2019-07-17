// See LICENSE for license details.

package treadle.symbolic

import org.scalatest.{Matchers, FreeSpec}
import uclid.smt

//scalastyle:off magic.number
class SymbolicContextSpec extends FreeSpec with Matchers {
  val ctx = new SymbolicContext()

  "evaluate concrete SMT BV formula" in {
    val one = smt.BitVectorLit(1, 2)
    val two = smt.BitVectorLit(2, 2)
    val one_plus_two = smt.OperatorApplication(smt.BVAddOp(2), List(one, two))
    val two_plus_two = smt.OperatorApplication(smt.BVAddOp(2), List(two, two))

    ctx.eval(one_plus_two, false) should be (BigInt(3))
    ctx.eval(one_plus_two, true) should be (BigInt(3))
    ctx.eval(two_plus_two, false) should be (BigInt(0))
    ctx.eval(two_plus_two, true) should be (BigInt(0))
  }

  "evaluate concrete SMT boolean formula" in {
    val tru  = smt.BooleanLit(true)
    val fals = smt.BooleanLit(false)

    val tru_and_fals = smt.OperatorApplication(smt.ConjunctionOp, List(tru, fals))
    val tru_and_tru  = smt.OperatorApplication(smt.ConjunctionOp, List(tru, tru))
    val tru_or_fals  = smt.OperatorApplication(smt.DisjunctionOp, List(tru, fals))
    val tru_or_tru   = smt.OperatorApplication(smt.DisjunctionOp, List(tru, tru))
    val fals_or_fals = smt.OperatorApplication(smt.DisjunctionOp, List(fals, fals))


    ctx.eval(tru_and_fals) should be (BigInt(0))
    ctx.eval(tru_and_tru)  should be (BigInt(1))
    ctx.eval(tru_or_fals)  should be (BigInt(1))
    ctx.eval(tru_or_tru)   should be (BigInt(1))
    ctx.eval(fals_or_fals) should be (BigInt(0))
  }

}
