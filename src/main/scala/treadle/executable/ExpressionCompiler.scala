// See LICENSE for license details.

package treadle.executable

trait AbstractExpressionCompiler {
  def compile(circuit: Circuit, blackBoxFactories: Seq[ScalaBlackBoxFactory]): Unit
  def makeGet(source: Symbol): ExpressionResult
  def makeGetIndirect(memory: Symbol, data: Symbol, enable: Symbol, addr: Symbol): ExpressionResult
  def makeAssigner(symbol: Symbol, expressionResult: ExpressionResult, conditionalClockSymbol: Option[Symbol] = None,
                   info: Info)
  def makeIndirectAssigner(portSymbol: Symbol, memorySymbol: Symbol, addr: Symbol, enable: Symbol,
                           expressionResult: ExpressionResult, clock: Symbol, info: Info)
  def makeAnd(e1: ExpressionResult, e2: ExpressionResult, resultWidth: Int): ExpressionResult
}
