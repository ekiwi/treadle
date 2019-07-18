// See LICENSE for license details.

package treadle.symbolic

import org.scalatest.{Matchers, FreeSpec}
import uclid.smt

//scalastyle:off magic.number
class ValueSummarySpec extends FreeSpec with Matchers {
  implicit val ctx = new SymbolicContext()

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
}
