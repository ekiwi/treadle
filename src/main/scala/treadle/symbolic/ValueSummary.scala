// See LICENSE for license details.

package treadle.symbolic

import net.sf.javabdd.{BDD, JFactory}
import uclid.smt

case class Entry(guard: BDD, concrete: Option[BigInt] = None, symbolic: Option[smt.Expr] = None) {
  def isConcrete : Boolean = concrete.isDefined
}

// TODO: add getter for concrete that crashes if concrete is not availale
// TODO: add getter for symbolic that converts concrete to symbolic if symbolic is not available
// TODO: add a switch to disable BDD simplification for benchmarking
// TODO: add a switch to compute SMT along with concrete values in order to verify SMT encoding

object Entry {
  def concrete(guard: BDD, value: BigInt) : Entry = Entry(guard, concrete = Some(value))
  def symbolic(guard: BDD, value: smt.Expr) : Entry = Entry(guard, symbolic = Some(value))
}

class ValueSummary(val entries: Seq[Entry])(val ctx: SymbolicContext) {

}

object ValueSummary {
  type ConcreteFun = (BigInt, BigInt) => BigInt
  type SymbolicFun = (smt.Expr, smt.Expr) => smt.Expr
  def binOp(a: ValueSummary, b: ValueSummary, con: ConcreteFun, sym: SymbolicFun) : ValueSummary = {
    for(e1 <- a.entries; e2 <- b.entries) {
      val guard = e1.guard.and(e1.guard)
      if(!guard.isZero) {
        if(e1.isConcrete && e2.isConcrete) {
          Entry.concrete(guard, con(e1.concrete.get, e2.concrete.get))
        } else {

        }
      }
    }

  }
}

