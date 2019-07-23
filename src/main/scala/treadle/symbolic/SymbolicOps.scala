// See LICENSE for license details.

package treadle.symbolic

import treadle.utils.{BitMasks, BitUtils}

import treadle.executable._


trait SymbolicExpressionResult extends ExpressionResult {
  def apply(): ValueSummary
}

object SymbolicExpressionResult {
  def apply(e: ExpressionResult): SymbolicExpressionResult = {
    assert(e.isInstanceOf[SymbolicExpressionResult], s"result e is not of symbolic type! $e")
    e.asInstanceOf[SymbolicExpressionResult]
  }
}
case class GetSymConstant(n: ValueSummary) extends SymbolicExpressionResult {
  def apply(): ValueSummary = n
}
