// See LICENSE for license details.

package treadle.symbolic

import org.scalatest.{Matchers, FreeSpec}
import uclid.smt

//scalastyle:off magic.number
class ValueSummarySpec extends FreeSpec with Matchers {
  implicit val ctx = new SymbolicContext()

  private def bv4(value: Int) = ValueSummary(value, 4)
  private def bv4_add_sym(a: smt.Expr, b: smt.Expr) = smt.OperatorApplication(smt.BVAddOp(4), List(a,b))
  private def add_con(a: BigInt, b: BigInt) = a + b

  "pruning of infeasible entries" in {
    // for this test we create a `false` guard in the value summary
    val a = ValueSummary(smt.Symbol("a", smt.BoolType))
    val four_or_five = ValueSummary.ite(a, bv4(4), bv4(5))
    val one_or_one = ValueSummary.ite(a, bv4(1), bv4(1))

    // if we add the two value summaries, we should get no more than two entries,
    // since the other entries should evaluate to false
    val sum = ValueSummary.binOp(four_or_five, one_or_one, add_con, bv4_add_sym, 4)
    sum.entryCount should be (2)
  }

  "coalescing of duplicate values" in {
    val a = ValueSummary(smt.Symbol("a", smt.BoolType))
    val four_or_five = ValueSummary.ite(a, bv4(4), bv4(5))
    val one_or_zero = ValueSummary.ite(a, bv4(1), bv4(0))

    // the result of the addition is always five, no matter what the branch condition is
    val sum = ValueSummary.binOp(four_or_five, one_or_zero, add_con, bv4_add_sym, 4)
    sum.entryCount should be (1)
  }

  "concrete ite" in {
    val tru = ValueSummary(true)
    val fals = ValueSummary(false)
    val four = ValueSummary(4, 4)
    val five = ValueSummary(5, 4)

    ValueSummary.ite(tru,  four, five).isConcrete should be (true)
    ValueSummary.ite(tru,  four, five).concrete should be (BigInt(4))
    ValueSummary.ite(fals, four, five).isConcrete should be (true)
    ValueSummary.ite(fals, four, five).concrete should be (BigInt(5))
  }

  "concrete unop" in {
    val four = ValueSummary(4, 4)

    ValueSummary.unOp(four, a => a + 5, a => a, 5).isConcrete should be (true)
    ValueSummary.unOp(four, a => a + 5, a => a, 5).concrete should be (BigInt(9))
    ValueSummary.unOp(four, a => a + 5, a => a, 5).width should be (5)
  }

  "concrete binop" in {
    val four = ValueSummary(4, 4)
    val five = ValueSummary(5, 4)

    val add_sym : ValueSummary.SymbolicFun = (a,b) => smt.OperatorApplication(smt.BVAddOp(4), List(a, b))

    ValueSummary.binOp(four, five, (a,b) => a + b, add_sym, 4).isConcrete should be (true)
    ValueSummary.binOp(four, five, (a,b) => a + b, add_sym, 4).concrete should be (BigInt(9))
    ValueSummary.binOp(four, five, (a,b) => a + b, add_sym, 4).width should be (4)
  }

  "toString" in {
    ValueSummary(true).toString should be ("true")
    ValueSummary(false).toString should be ("false")
    ValueSummary(4, 4).toString should be ("4")

    val a = smt.Symbol("a", smt.BoolType)
    val b = smt.Symbol("b", smt.BoolType)
    val c = smt.Symbol("c", smt.BoolType)
    val a_and_b = smt.OperatorApplication(smt.ConjunctionOp, List(a,b))
    val ite_cab = smt.OperatorApplication(smt.ITEOp, List(c, a, b))
    ValueSummary(a).toString should be ("a")
    ValueSummary(a_and_b).toString should be ("(and a b)")
    ValueSummary(ite_cab).toString should be ("(ite c a b)")
    val vs_ite = ValueSummary.ite(ValueSummary(c), ValueSummary(a), ValueSummary(b))
    vs_ite.toString should be ("(ite c a b)")
  }
}
