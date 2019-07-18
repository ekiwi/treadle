// See LICENSE for license details.

package treadle.symbolic

import net.sf.javabdd.{BDD, JFactory}
import uclid.smt

class Entry private(val guard: BDD, val width: Int, private val con: Option[BigInt] = None,
                    private val sym: Option[smt.Expr] = None) {
  def isConcrete : Boolean = con.isDefined
  def concrete : BigInt = {
    assert(isConcrete, "not concrete!")
    con.get
  }
  def symbolic : smt.Expr = if(isConcrete) {
    if(width == 1) { smt.BooleanLit(con.get == BigInt(1)) } else { smt.BitVectorLit(con.get, width) }
  } else { sym.get }
  def updateGuard(newGuard: BDD) : Entry = {
    new Entry(newGuard, width, con, sym)
  }
}

object Entry {
  private def bits(e: smt.Expr) : Int = if(e.typ.isBool) { 1 } else {
    assert(e.typ.isBitVector, s"unsupported type `$e.typ` of expressions: $e")
    e.typ.asInstanceOf[smt.BitVectorType].width
  }
  def apply(guard: BDD, value: BigInt, width: Int) : Entry = new Entry(guard, width, con = Some(value))
  def apply(guard: BDD, value: smt.Expr) : Entry = new Entry(guard, bits(value), sym = Some(value))
}

class ValueSummary private(private val ctx: SymbolicContext, private val entries: Seq[Entry]) {
  assert(entries.nonEmpty, s"entries must contain at least one element: $entries")
  assert(entries.forall(_.width == entries.head.width), s"entries are not of equal witdth: $entries")
  def width : Int = entries.head.width
  def isConcrete : Boolean = entries.size == 1 && entries.head.isConcrete
  def concrete : BigInt = {
    assert(isConcrete, "not concrete!")
    entries.head.concrete
  }
  def symbolic : smt.Expr = {
    if(entries.size == 1) { entries.head.symbolic } else {
      entries.drop(1).foldLeft(entries.head.symbolic) { (a: smt.Expr, b: Entry) =>
        val cond = ctx.bddToSmt(b.guard)
        smt.OperatorApplication(smt.ITEOp, List(cond, b.symbolic, a))
      }
    }
  }
  override def toString : String = {
    if(isConcrete) { concrete.toString() }
    else { symbolic.toString }
  }
}


// TODO: implement computing SMT along with concrete values in order to verify SMT encoding
//       (see ctx.CrosscheckSmtWithConcrete)

object ValueSummary {
  def apply(value: BigInt, width: Int)(implicit ctx: SymbolicContext) : ValueSummary = {
    new ValueSummary(ctx, Seq(Entry(ctx.tru, value, width)))
  }
  def apply(value: Boolean)(implicit ctx: SymbolicContext) : ValueSummary = {
    ValueSummary(if(value) {BigInt(1) } else { BigInt(0) }, 1)(ctx)
  }
  def apply(value: smt.Expr)(implicit ctx: SymbolicContext) : ValueSummary = {
    new ValueSummary(ctx, Seq(Entry(ctx.tru, value)))
  }

  type ConcreteFun = (BigInt, BigInt) => BigInt
  type SymbolicFun = (smt.Expr, smt.Expr) => smt.Expr
  def binOp(a: ValueSummary, b: ValueSummary, con: ConcreteFun, sym: SymbolicFun, width: Int) : ValueSummary = {
    lazy val gee = for(e1 <- a.entries; e2 <- b.entries) yield { (e1.guard.and(e2.guard), e1, e2) }
    val ee = gee.filter(!_._1.isZero).map{ case (guard, e1, e2) =>
      if(e1.isConcrete && e2.isConcrete) {
        Entry(guard, con(e1.concrete, e2.concrete), width)
      } else {
        Entry(guard, sym(e1.symbolic, e2.symbolic))
      }
    }
    assert(a.ctx == b.ctx)
    val entries = if(a.ctx.DoNotCoalesce) { ee } else { coalesce(ee) }
    new ValueSummary(a.ctx, entries)
  }

  def unOp(a: ValueSummary, con: BigInt => BigInt, sym: smt.Expr => smt.Expr, width: Int) : ValueSummary = {
    val entries : Seq[Entry] = a.entries.map { e =>
      if(e.isConcrete) { Entry(e.guard, con(e.concrete), width) }
      else { Entry(e.guard, sym(e.symbolic)) }
    }
    new ValueSummary(a.ctx, entries)
  }

  def ite(cond: ValueSummary, tru: ValueSummary, fals: ValueSummary) : ValueSummary = {
    assert(cond.width == 1, s"Condition needs to be boolean: $cond")
    assert(tru.width == fals.width, s"both sides of a mux need to be of the same width: $tru vs $fals")
    assert(cond.ctx == tru.ctx && tru.ctx == fals.ctx)
    val ctx = cond.ctx

    val tru_cond  = cond.entries.map { ce => ctx.smtToBdd(ce.symbolic).and(ce.guard) }.filter(!_.isZero)
    val fals_cond = cond.entries.map { ce => ctx.smtToBdd(ce.symbolic).not().and(ce.guard) }.filter(!_.isZero)


    def select(conds: Seq[BDD], v: ValueSummary) : Seq[Entry] = {
      val ee = for(c <- conds; ve <- v.entries) yield {
        val guard = c.and(ve.guard)
        if(!guard.isZero) { Some(ve.updateGuard(guard)) } else { None }
      }
      ee.flatten
    }

    val ee = select(tru_cond, tru) ++ select(fals_cond, fals)
    val entries = if(ctx.DoNotCoalesce) { ee } else { coalesce(ee) }
    new ValueSummary(ctx, entries)
  }

  private def coalesce(entries: Seq[Entry]) : Seq[Entry] = {
    // TODO: implement
    entries
  }
}

