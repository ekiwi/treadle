// See LICENSE for license details.

package treadle.symbolic

import firrtl.PrimOps._
import firrtl.ir._
import treadle._
import treadle.executable._




class SymbolicExpressionCompiler(
  symbolTable  : SymbolTable,
  override val dataStore    : SymbolicDataStore,
  scheduler        : Scheduler,
  treadleOptions   : TreadleOptions,
  blackBoxFactories: Seq[ScalaBlackBoxFactory]
)
extends ExpressionCompiler(symbolTable, dataStore, scheduler, treadleOptions, blackBoxFactories) {

  override def makeGet(source: Symbol): ExpressionResult = {
    dataStore.Get(source.index)
  }

  override def makeGetIndirect(memory: Symbol, data: Symbol, enable: Symbol, addr: Symbol): ExpressionResult = {
    dataStore.GetIndirect(
      memory, dataStore.Get(addr.index).apply, dataStore.Get(enable.index).apply
    )
  }

  //scalastyle:off cyclomatic.complexity
  override def createAssigner(
                    symbol: Symbol,
                    expressionResult: ExpressionResult,
                    info: Info
                  ): Assigner = {
    val result = SymbolicExpressionResult(expressionResult)
    if(scheduler.isTrigger(symbol)) {
      dataStore.TriggerIntAssigner(symbol, scheduler, result.apply, triggerOnValue = 1, info)
    } else {
      dataStore.Assign(symbol, result.apply, info)
    }
  }

  override def makeAssigner(
                             symbol: Symbol,
                             expressionResult: ExpressionResult,
                             triggerOption: Option[Symbol] = None,
                             info: Info
                           ): Unit = {
    addAssigner(createAssigner(symbol, expressionResult, info), triggerOption)
  }

  override def makeIndirectAssigner(
                            portSymbol       : Symbol,
                            memorySymbol     : Symbol,
                            memoryIndex      : Int,
                            enableIndex      : Int,
                            expressionResult : ExpressionResult,
                            clock            : Symbol,
                            info             : Info
                          ): Unit = {

    def getIndex = dataStore.Get(memoryIndex).apply _
    def getEnable = dataStore.Get(enableIndex).apply _
    val assigner = dataStore.AssignIntIndirect(portSymbol, memorySymbol, getIndex, getEnable, result.apply, info)
    addAssigner(assigner)
  }


  override def makeAnd(e1: ExpressionResult, e2: ExpressionResult, resultWidth: Int): ExpressionResult = {
    val a = SymbolicExpressionResult(e1)
    val b = SymbolicExpressionResult(e2)
    AndSym(a.apply, b.apply, resultWidth)
  }

  //scalastyle:off method.length
  override def binaryOps(modulePrefix: String, opCode: PrimOp, args: Seq[Expression], tpe: Type): ExpressionResult = {

    def getParameters(e: Expression) =
      (processExpression(modulePrefix, e), getSigned(e), getWidth(e))

    val (arg1, _, arg1Width) = getParameters(args.head)
    val (arg2, _, arg2Width) = getParameters(args.tail.head)

    def handleIntResult(e1: IntExpressionResult, e2: IntExpressionResult): ExpressionResult = {
      opCode match {
        case Add => AddInts(e1.apply, e2.apply)
        case Sub => SubInts(e1.apply, e2.apply)
        case Mul => MulInts(e1.apply, e2.apply)
        case Div => DivInts(e1.apply, e2.apply)
        case Rem => RemInts(e1.apply, e2.apply)

        case Eq  => EqInts(e1.apply,  e2.apply)
        case Neq => NeqInts(e1.apply, e2.apply)
        case Lt  => LtInts(e1.apply,  e2.apply)
        case Leq => LeqInts(e1.apply, e2.apply)
        case Gt  => GtInts(e1.apply,  e2.apply)
        case Geq => GeqInts(e1.apply, e2.apply)

        case Dshl => DshlInts(e1.apply, e2.apply)
        case Dshr => DshrInts(e1.apply, e2.apply)

        case And => AndInts(e1.apply, e2.apply, arg1Width.max(arg2Width))
        case Or  => OrInts(e1.apply,  e2.apply, arg1Width.max(arg2Width))
        case Xor => XorInts(e1.apply, e2.apply, arg1Width.max(arg2Width))

        case Cat =>
          CatInts(e1.apply, arg1Width, e2.apply, arg2Width)

        case _ =>
          throw TreadleException(s"Error:BinaryOp:$opCode)(${args.head}, ${args.tail.head})")
      }
    }

    def handleLongResult(e1: LongExpressionResult, e2: LongExpressionResult): ExpressionResult = {
      opCode match {
        case Add => AddLongs(e1.apply, e2.apply)
        case Sub => SubLongs(e1.apply, e2.apply)
        case Mul => MulLongs(e1.apply, e2.apply)
        case Div => DivLongs(e1.apply, e2.apply)
        case Rem => RemLongs(e1.apply, e2.apply)

        case Eq  => EqLongs(e1.apply, e2.apply)
        case Neq => NeqLongs(e1.apply, e2.apply)
        case Lt  => LtLongs(e1.apply, e2.apply)
        case Leq => LeqLongs(e1.apply, e2.apply)
        case Gt  => GtLongs(e1.apply, e2.apply)
        case Geq => GeqLongs(e1.apply, e2.apply)

        case Dshl => DshlLongs(e1.apply, e2.apply)
        case Dshr => DshrLongs(e1.apply, e2.apply)

        case And  => AndLongs(e1.apply, e2.apply, arg1Width.max(arg2Width))
        case Or   => OrLongs(e1.apply, e2.apply, arg1Width.max(arg2Width))
        case Xor  => XorLongs(e1.apply, e2.apply, arg1Width.max(arg2Width))

        case Cat =>
          CatLongs(e1.apply, arg1Width, e2.apply, arg2Width)

        case _ =>
          throw TreadleException(s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head})")
      }
    }

    def handleBigResult(e1: BigExpressionResult, e2: BigExpressionResult): ExpressionResult = {
      opCode match {
        case Add => AddBigs(e1.apply, e2.apply)
        case Sub => SubBigs(e1.apply, e2.apply)
        case Mul => MulBigs(e1.apply, e2.apply)
        case Div => DivBigs(e1.apply, e2.apply)
        case Rem => RemBigs(e1.apply, e2.apply)

        case Eq  => EqBigs(e1.apply, e2.apply)
        case Neq => NeqBigs(e1.apply, e2.apply)
        case Lt  => LtBigs(e1.apply, e2.apply)
        case Leq => LeqBigs(e1.apply, e2.apply)
        case Gt  => GtBigs(e1.apply, e2.apply)
        case Geq => GeqBigs(e1.apply, e2.apply)

        case Dshl => DshlBigs(e1.apply, e2.apply)
        case Dshr => DshrBigs(e1.apply, e2.apply)

        case And  => AndBigs(e1.apply, e2.apply, arg1Width.max(arg2Width))
        case Or   => OrBigs(e1.apply, e2.apply, arg1Width.max(arg2Width))
        case Xor  => XorBigs(e1.apply, e2.apply, arg1Width.max(arg2Width))

        case Cat =>
          CatBigs(e1.apply, arg1Width, e2.apply, arg2Width)

        case _ =>
          throw TreadleException(s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head})")
      }
    }

    (DataSize(getWidth(tpe)), arg1, arg2) match {

      case (IntSize,  e1: IntExpressionResult, e2: IntExpressionResult) =>
        handleIntResult(e1, e2)

      case (IntSize, e1: LongExpressionResult, e2: IntExpressionResult) =>
        handleLongResult(e1, ToLong(e2.apply))
      case (IntSize, e1: BigExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(e1, ToBig(e2.apply))

      case (IntSize, e1: IntExpressionResult, e2: LongExpressionResult) =>
        handleLongResult(ToLong(e1.apply), e2)
      case (IntSize, e1: LongExpressionResult, e2: LongExpressionResult) =>
        handleLongResult(e1, e2)
      case (IntSize, e1: BigExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(e1, LongToBig(e2.apply))

      case (IntSize, e1: IntExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(ToBig(e1.apply), e2)
      case (IntSize, e1: LongExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(LongToBig(e1.apply), e2)
      case (IntSize, e1: BigExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(e1, e2)
      case (IntSize, _, _) =>
        throw TreadleException(
          s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head}) ($arg1, $arg2)")

      case (LongSize, e1: IntExpressionResult, e2: IntExpressionResult) =>
        handleLongResult(ToLong(e1.apply), ToLong(e2.apply))
      case (LongSize, e1: LongExpressionResult, e2: IntExpressionResult) =>
        handleLongResult(e1, ToLong(e2.apply))
      case (LongSize, e1: BigExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(e1, ToBig(e2.apply))

      case (LongSize, e1: IntExpressionResult, e2: LongExpressionResult) =>
        handleLongResult(ToLong(e1.apply), e2)
      case (LongSize, e1: LongExpressionResult, e2: LongExpressionResult) =>
        handleLongResult(e1, e2)
      case (LongSize, e1: BigExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(e1, LongToBig(e2.apply))

      case (LongSize, e1: IntExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(ToBig(e1.apply), e2)
      case (LongSize, e1: LongExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(LongToBig(e1.apply), e2)
      case (LongSize, e1: BigExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(e1, e2)
      case (LongSize, _, _) =>
        throw TreadleException(
          s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head}) ($arg1, $arg2)")

      case (BigSize, e1: IntExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(ToBig(e1.apply), ToBig(e2.apply))
      case (BigSize, e1: LongExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(LongToBig(e1.apply), ToBig(e2.apply))
      case (BigSize, e1: BigExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(e1, ToBig(e2.apply))

      case (BigSize, e1: IntExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(ToBig(e1.apply), LongToBig(e2.apply))
      case (BigSize, e1: LongExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(LongToBig(e1.apply), LongToBig(e2.apply))
      case (BigSize, e1: BigExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(e1, LongToBig(e2.apply))

      case (BigSize, e1: IntExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(ToBig(e1.apply), e2)
      case (BigSize, e1: LongExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(LongToBig(e1.apply), e2)
      case (BigSize, e1: BigExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(e1, e2)

      case (BigSize, _, _) =>
        throw TreadleException(
          s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head}) ($arg1, $arg2)")
    }
  }

  override def oneArgOneParamOps(modulePrefix: String,
                                 op: PrimOp,
                         expressions: Seq[Expression],
                         ints: Seq[BigInt],
                         tpe: firrtl.ir.Type
                       ): ExpressionResult = {
    val arg1 = processExpression(modulePrefix, expressions.head)
    val arg1Width = getWidth(expressions.head)
    val param1 = ints.head.toInt

    arg1 match {
      case e1: IntExpressionResult =>
        op match {
          case Head => HeadInts(e1.apply, takeBits = param1, arg1Width)
          case Tail => TailInts(e1.apply, toDrop = param1, arg1Width)
          case Shl  => ShlInts(e1.apply, GetIntConstant(param1).apply)
          case Shr  => ShrInts(e1.apply, GetIntConstant(param1).apply)
        }
      case e1: LongExpressionResult =>
        op match {
          case Head => HeadLongs(e1.apply, takeBits = param1, arg1Width)
          case Tail => TailLongs(e1.apply, toDrop = param1, arg1Width)
          case Shl  => ShlLongs(e1.apply, GetLongConstant(param1).apply)
          case Shr  => ShrLongs(e1.apply, GetLongConstant(param1).apply)
        }
      case e1: BigExpressionResult =>
        op match {
          case Head => HeadBigs(e1.apply, takeBits = param1, arg1Width)
          case Tail => TailBigs(e1.apply, toDrop = param1, arg1Width)
          case Shl  => ShlBigs(e1.apply, GetBigConstant(param1).apply)
          case Shr  => ShrBigs(e1.apply, GetBigConstant(param1).apply)
        }
    }
  }

  override def oneArgTwoParamOps(modulePrefix: String,
                                 op: PrimOp,
                         expressions: Seq[Expression],
                         ints: Seq[BigInt],
                         tpe: firrtl.ir.Type
                       ): ExpressionResult = {
    val arg1 = processExpression(modulePrefix, expressions.head)
    val arg2 = ints.head
    val arg3 = ints.tail.head
    val width = tpe match {
      case UIntType(IntWidth(n)) => n.toInt
      case SIntType(IntWidth(n)) => n.toInt
    }

    arg1 match {
      case e1: IntExpressionResult =>
        op match {
          case Bits => BitsInts(e1.apply, arg2.toInt, arg3.toInt, width)
        }
      case e1: LongExpressionResult =>
        op match {
          case Bits => BitsLongs(e1.apply, arg2.toInt, arg3.toInt, width)
        }
      case e1: BigExpressionResult =>
        op match {
          case Bits => BitsBigs(e1.apply, arg2.toInt, arg3.toInt, width)
        }
    }
  }

  override def unaryOps(modulePrefix: String,
                        op: PrimOp,
                expressions: Seq[Expression],
                tpe: firrtl.ir.Type
              ): ExpressionResult = {
    val arg1 = processExpression(modulePrefix, expressions.head)

    val width = tpe match {
      case UIntType(IntWidth(n)) => n.toInt
      case SIntType(IntWidth(n)) => n.toInt
      case ClockType             => 1
    }

    arg1 match {
      case e1: IntExpressionResult =>
        op match {
          case Pad     => e1
          case AsUInt  => AsUIntInts(e1.apply, width)
          case AsSInt  => AsSIntInts(e1.apply, width)
          case AsClock => e1

          case Cvt     => e1
          case Neg     => NegInts(e1.apply)
          case Not     => NotInts(e1.apply, width)

          case Andr    => AndrInts(e1.apply, width)
          case Orr     => OrrInts(e1.apply,  width)
          case Xorr    => XorrInts(e1.apply, width)
        }
      case e1: LongExpressionResult =>
        op match {
          case Pad     => e1
          case AsUInt  => AsUIntLongs(e1.apply, width)
          case AsSInt  => AsSIntLongs(e1.apply, width)
          case AsClock => e1

          case Cvt     => e1
          case Neg     => NegLongs(e1.apply)
          case Not     => NotLongs(e1.apply, width)

          case Andr    => AndrLongs(e1.apply, width)
          case Orr     => OrrLongs(e1.apply,  width)
          case Xorr    => XorrLongs(e1.apply, width)
        }
      case e1: BigExpressionResult =>
        op match {
          case Pad     => e1
          case AsUInt  => AsUIntBigs(e1.apply, width)
          case AsSInt  => AsSIntBigs(e1.apply, width)
          case AsClock => e1

          case Cvt     => e1
          case Neg     => NegBigs(e1.apply)
          case Not     => NotBigs(e1.apply, width)

          case Andr    => AndrBigs(e1.apply, width)
          case Orr     => OrrBigs(e1.apply,  width)
          case Xorr    => XorrBigs(e1.apply, width)
        }
    }
  }

  override def processMux(
                  condition: ExpressionResult,
                  trueExpression: ExpressionResult,
                  falseExpression: ExpressionResult
                ): ExpressionResult = {

    condition match {
      case c: IntExpressionResult =>
        (trueExpression, falseExpression) match {

          case (t: IntExpressionResult, f: IntExpressionResult) =>
            MuxInts(c.apply, t.apply, f.apply)
          case (t: IntExpressionResult, f: LongExpressionResult) =>
            MuxLongs(c.apply, ToLong(t.apply).apply, f.apply)
          case (t: IntExpressionResult, f: BigExpressionResult) =>
            MuxBigs(c.apply, ToBig(t.apply).apply, f.apply)

          case (t: LongExpressionResult, f: IntExpressionResult) =>
            MuxLongs(c.apply, t.apply, ToLong(f.apply).apply)
          case (t: LongExpressionResult, f: LongExpressionResult) =>
            MuxLongs(c.apply, t.apply, f.apply)
          case (t: LongExpressionResult, f: BigExpressionResult) =>
            MuxBigs(c.apply, LongToBig(t.apply).apply, f.apply)

          case (t: BigExpressionResult, f: IntExpressionResult) =>
            MuxBigs(c.apply, t.apply, ToBig(f.apply).apply)
          case (t: BigExpressionResult, f: LongExpressionResult) =>
            MuxBigs(c.apply, t.apply, LongToBig(f.apply).apply)
          case (t: BigExpressionResult, f: BigExpressionResult) =>
            MuxBigs(c.apply, t.apply, f.apply)
        }
      case c =>
        throw TreadleException(s"Mux condition is not 1 bit $condition parsed as $c")
    }
  }
}
