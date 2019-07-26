// See LICENSE for license details.

package treadle.executable

import firrtl.ir.Info

trait StopConditionResult extends ExpressionResult {
  def apply() : Boolean
}

case class StopOp(
  symbol             : Symbol,
  info               : Info,
  returnValue        : Int,
  condition          : StopConditionResult,
  hasStopped         : Symbol,
  dataStore          : DataWriter,
  clockTransition    : AbstractClockTransitionGetter
) extends Assigner {

  def run: FuncUnit = {
    val conditionValue = condition.apply()
    if (conditionValue && clockTransition.isPosEdge) {
      if (isVerbose) {
        println(s"clock ${symbol.name} has fired")
      }
      dataStore.update(hasStopped, returnValue + 1)
    }

    () => Unit
  }
}

object StopOp {
  val stopHappenedName = "/stopped"
}

case class StopInfo(stopSymbol: Symbol)
