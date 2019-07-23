// See LICENSE for license details.

package treadle.symbolic

import firrtl.ir._
import uclid.smt
import treadle.utils.{BitMasks, BitUtils}

trait Semantics {
  val argCount : Int
  def resultType(ts: Seq[Type]) : Option[Type]
}

trait BinOpSemantics extends Semantics {
  override val argCount = 2

  override def resultType(ts: Seq[Type]) : Option[Type] = {
    assert(ts.size == 2)
    resultType(ts.head, ts(1))
  }

  def resultType(t1: Type, t2: Type) : Option[Type] = (t1, t2) match {
    case (UIntType(IntWidth(w1)), UIntType(IntWidth(w2))) =>
      Some(UIntType(IntWidth(uIntResultWidth(w1, w2))))
    case (SIntType(IntWidth(w1)), SIntType(IntWidth(w2))) =>
      Some(SIntType(IntWidth(sIntResultWidth(w1, w2))))
    case _ => None
  }

  type ConFun = (BigInt, BigInt) => BigInt
  type SymFun = (smt.Expr, smt.Expr) => smt.Expr

  def compileCon(w1: Int, w2: Int, wr: Int) : ConFun

  def typeCheck(t1: Type, t2: Type, tr: Type) : Boolean = resultType(t1,t2).contains(tr)

  def compile(t1: Type, t2: Type, tr: Type) : (ConFun, SymFun) = {
    val (w1, w2, wr) = (getWidth(t1), getWidth(t2), getWidth(tr))
    (compileCon(w1, w2, wr), compileSym(w1, w2, wr, isSigned(tr)))
  }

  def compileAndCheck(t1: Type, t2: Type, tr: Type) : (ConFun, SymFun) = {
    assert(typeCheck(t1, t2, tr), "Expressions does not type-check!")
    assert(getWidth(t1) > 0 && getWidth(t2) > 0, s"No support for 0-width types! ($t1, $t2, $tr)")
    compile(t1, t2, tr)
  }

  protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun

  protected def uIntResultWidth(w1: BigInt, w2: BigInt) : BigInt
  protected def sIntResultWidth(w1: BigInt, w2: BigInt) : BigInt

  protected def getWidth(tpe: Type) : Int = tpe match {
    case UIntType(IntWidth(w)) => w.toInt
    case SIntType(IntWidth(w)) => w.toInt
    case other => throw new RuntimeException(s"Cannot get width for type: $other")
  }

  protected def isSigned(tpe: Type): Boolean = tpe match {
    case SIntType(_) => true
    case _ => false
  }

  protected def extend(inBits: Int, outBits: Int, signed: Boolean) : smt.Expr => smt.Expr = {
    assert(inBits <= outBits,  "This method only extends the width of an argument!")
    if(inBits == outBits) { _ }
    else{
      val op = if(signed){ smt.BVSignExtOp(outBits, outBits - inBits) }
      else { smt.BVZeroExtOp(outBits, outBits - inBits) }
      e => smt.OperatorApplication(op, List(e))
    }
  }

}

trait ArithmeticSemantics extends BinOpSemantics {
  protected def op(w: Int) : smt.Operator
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = (a,b) => {
    smt.OperatorApplication(op(wr), List(extend(w1, wr, signed)(a), extend(w1, wr, signed)(b)))
  }
}

object AddSemantics extends ArithmeticSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2) + 1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2) + 1
  override protected def op(w: Int) = smt.BVAddOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 + e2
}

object SubSemantics extends ArithmeticSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2) + 1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2) + 1
  override protected def op(w: Int) = smt.BVSubOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 - e2
}

object MulSemantics extends ArithmeticSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1 + w2
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1 + w2
  override protected def op(w: Int) = smt.BVMulOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 * e2
}

trait RemDivSemantics extends BinOpSemantics {
  protected def op(w: Int) : smt.Operator
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = (a,b) => {
    val e2 = extend(w1, wr, signed)(b)
    val zero = smt.BitVectorLit(0, wr)
    val is_zero = smt.OperatorApplication(smt.EqualityOp, List(e2, zero))
    val res = smt.OperatorApplication(op(wr), List(extend(w1, wr, signed)(a), e2))
    smt.OperatorApplication(smt.ITEOp, List(is_zero, zero, res))
  }
}

object DivSemantics extends RemDivSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1 + 1
  override protected def op(w: Int) =
    throw new NotImplementedError("BVDivOp is only available in an unpublished version of Uclid")//smt.BVDivOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e2 == 0) { 0 } else { e1 / e2}
}

object RemSemantics extends RemDivSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1.min(2)
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1.min(2)
  override protected def op(w: Int) =
    throw new NotImplementedError("BVRemOp is only available in an unpublished version of Uclid")//smt.BVRemOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e2 == 0) { 0 } else { e1 % e2}
}

trait ComparisonSemantics extends BinOpSemantics {
  protected def op(signed: Boolean) : smt.Operator
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = 1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = 1
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = {
    val we = math.max(w1, w2)
    (a,b) => {
      smt.OperatorApplication(op(signed), List(extend(w1, we, signed)(a), extend(w1, we, signed)(b)))
    }
  }
}

object EqSemantics extends ComparisonSemantics {
  override protected def op(signed: Boolean) = smt.EqualityOp
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 == e2) { 1 } else { 0 }
}

object NeqSemantics extends ComparisonSemantics {
  override protected def op(signed: Boolean) = smt.InequalityOp
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 != e2) { 1 } else { 0 }
}

object LtSemantics extends ComparisonSemantics {
  override protected def op(signed: Boolean) = if(signed) { smt.BVLTOp(1) } else { smt.BVLTUOp(1) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 < e2) { 1 } else { 0 }
}

object LeqSemantics extends ComparisonSemantics {
  override protected def op(signed: Boolean) = if(signed) { smt.BVLEOp(1) } else { smt.BVLEUOp(1) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 <= e2) { 1 } else { 0 }
}

object GtSemantics extends ComparisonSemantics {
  override protected def op(signed: Boolean) = if(signed) { smt.BVGTOp(1) } else { smt.BVGTUOp(1) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 > e2) { 1 } else { 0 }
}

object GeqSemantics extends ComparisonSemantics {
  override protected def op(signed: Boolean) = if(signed) { smt.BVGEOp(1) } else { smt.BVGEUOp(1) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => if(e1 >= e2) { 1 } else { 0 }
}

trait BitwiseSemantics extends ArithmeticSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2)
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1.max(w2)
}

object AndSemantics extends BitwiseSemantics {
  override protected def op(w: Int) = smt.BVAndOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = {
    val mask = BitUtils.makeMaskBig(wr)
    (e1, e2) => (e1 & e2) & mask
  }
}

object OrSemantics extends BitwiseSemantics {
  override protected def op(w: Int) = smt.BVOrOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = {
    val mask = BitUtils.makeMaskBig(wr)
    (e1, e2) => (e1 | e2) & mask
  }
}

object XorSemantics extends BitwiseSemantics {
  override protected def op(w: Int) = smt.BVXorOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = {
    val mask = BitUtils.makeMaskBig(wr)
    (e1, e2) => (e1 ^ e2) & mask
  }
}

trait DynamicShiftSemantics extends BinOpSemantics {
  override def resultType(t1: Type, t2: Type) : Option[Type] = (t1, t2) match {
    case (UIntType(IntWidth(w1)), UIntType(IntWidth(w2))) =>
      Some(UIntType(IntWidth(uIntResultWidth(w1, w2))))
    case (SIntType(IntWidth(w1)), UIntType(IntWidth(w2))) =>
      Some(SIntType(IntWidth(sIntResultWidth(w1, w2))))
    case _ => None
  }
  protected def op(w: Int, signed: Boolean) : smt.Operator
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = (a,b) => {
    smt.OperatorApplication(op(wr, signed), List(extend(w1, wr, signed)(a), extend(w1, wr, signed)(b)))
  }
}

object DshlSemantics extends DynamicShiftSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1 + BigInt(2).pow(w2.toInt) - 1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1 + BigInt(2).pow(w2.toInt) - 1
  override protected def op(w: Int, signed: Boolean) = smt.BVLeftShiftBVOp(w)
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 << e2.toInt
}

object DshrSemantics extends DynamicShiftSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1
  override protected def op(w: Int, signed: Boolean) =
    if(signed) { smt.BVARightShiftBVOp(w) } else { smt.BVLRightShiftBVOp(w) }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = (e1, e2) => e1 >> e2.toInt
}

object CatSemantics extends BinOpSemantics {
  override protected def uIntResultWidth(w1: BigInt, w2: BigInt) = w1 + w2
  override protected def sIntResultWidth(w1: BigInt, w2: BigInt) = w1 + w2
  override protected def compileSym(w1: Int, w2: Int, wr: Int, signed: Boolean) : SymFun = (a,b) => {
    smt.OperatorApplication(smt.BVConcatOp(wr), List(a, b))
  }
  override protected def compileCon(w1: Int, w2: Int, wr: Int) = {
    val mask1 = BitMasks.getBitMasksBigs(w1).allBitsMask
    (e1, e2) => ((e1 & mask1) << w2) | e2
  }
}
