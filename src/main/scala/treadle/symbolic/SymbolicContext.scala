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

  private val bdds = JFactory.init(100, 100)
  private var bddVarCount = 0
  val solver : smt.Context = new YicesInterface()


  private val smtToBddCache: mutable.HashMap[Hashable, BDD] = new mutable.HashMap()



  def smtToBDD(expr: smt.Expr) : BDD = {
    if(!smtToBddCache.contains(expr)) {
      if(bdds.varNum() <= bddVarCount) {
        bdds.setVarNum(bddVarCount + 1)
      }
      smtToBddCache(expr) = bdds.ithVar(bddVarCount)
      bddVarCount += 1
    }
    smtToBddCache(expr)
  }

  def bddToSMT(bdd: BDD) : smt.Expr = {
    if(bdd.`var`())
  }

}

case class SymbolicValue(name: String, cycle: Int, tpe: ir.Type, signal: String, sym: smt.Expr)
