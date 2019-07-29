// See LICENSE for license details.

package treadle.executable.fast

import firrtl.PrimOps._
import firrtl.ir._
import treadle._
import treadle.executable._

class Compiler(
    val symbolTable  : SymbolTable,
    private val dataStore : DataStore,
    scheduler        : Scheduler,
    validIfIsRandom  : Boolean,
    blackBoxFactories: Seq[ScalaBlackBoxFactory]
)
  extends BaseCompiler(symbolTable, dataStore, scheduler) with FirrtlHelpers{

  def getExpressionCompiler(expand: String => String): treadle.executable.ExpressionCompiler = {
    new fast.ExpressionCompiler(expand, this, validIfIsRandom)
  }

  def makeGet(source: Symbol): ExpressionResult = {
    source.dataSize match {
      case IntSize =>
        dataStore.GetInt(source.index)
      case LongSize =>
        dataStore.GetLong(source.index)
      case BigSize =>
        dataStore.GetBig(source.index)
    }
  }

  def makeGetIndirect(memory: Symbol, data: Symbol, enable: Symbol, addr: Symbol): ExpressionResult = {
    data.dataSize match {
      case IntSize =>
        dataStore.GetIntIndirect(
          memory, dataStore.GetInt(addr.index).apply _, dataStore.GetInt(enable.index).apply _
        )
      case LongSize =>
        dataStore.GetLongIndirect(
          memory, dataStore.GetInt(addr.index).apply _, dataStore.GetInt(enable.index).apply _
        )
      case BigSize =>
        dataStore.GetBigIndirect(
          memory, dataStore.GetInt(addr.index).apply _, dataStore.GetInt(enable.index).apply _
        )
    }
  }

  //scalastyle:off cyclomatic.complexity
  def processMux(condition: ExpressionResult, tru: ExpressionResult, fals: ExpressionResult): ExpressionResult = {

    condition match {
      case c: IntExpressionResult =>
        (tru, fals) match {

          case (t: IntExpressionResult, f: IntExpressionResult) =>
            MuxInts(c.apply _, t.apply _, f.apply _)
          case (t: IntExpressionResult, f: LongExpressionResult) =>
            MuxLongs(c.apply _, ToLong(t.apply _).apply _, f.apply _)
          case (t: IntExpressionResult, f: BigExpressionResult) =>
            MuxBigs(c.apply _, ToBig(t.apply _).apply _, f.apply _)

          case (t: LongExpressionResult, f: IntExpressionResult) =>
            MuxLongs(c.apply _, t.apply _, ToLong(f.apply _).apply _)
          case (t: LongExpressionResult, f: LongExpressionResult) =>
            MuxLongs(c.apply _, t.apply _, f.apply _)
          case (t: LongExpressionResult, f: BigExpressionResult) =>
            MuxBigs(c.apply _, LongToBig(t.apply _).apply _, f.apply _)

          case (t: BigExpressionResult, f: IntExpressionResult) =>
            MuxBigs(c.apply _, t.apply _, ToBig(f.apply _).apply _)
          case (t: BigExpressionResult, f: LongExpressionResult) =>
            MuxBigs(c.apply _, t.apply _, LongToBig(f.apply _).apply _)
          case (t: BigExpressionResult, f: BigExpressionResult) =>
            MuxBigs(c.apply _, t.apply _, f.apply _)

          case (a, b) =>
            throw TreadleException(s"Unhandled Mux($condition, $a, $b)")
        }
      case c =>
        throw TreadleException(s"Mux condition is not 1 bit $condition parsed as $c")
    }
  }

  def makeClockTransitionGetter(clockSymbol: Symbol, prevClockSymbol: Symbol): AbstractClockTransitionGetter =
    ClockTransitionGetter(clockSymbol, prevClockSymbol)

  case class ClockTransitionGetter(clockSymbol: Symbol, prevClockSymbol: Symbol) extends AbstractClockTransitionGetter {
    private val clockIndex = clockSymbol.index
    private val prevClockIndex = prevClockSymbol.index
    private val intData = dataStore.intData

    def getClockSymbol: Symbol = clockSymbol
    def isPosEdge: Boolean = intData(clockIndex) > 0 && intData(prevClockIndex) == 0
    def isNegEdge: Boolean = intData(clockIndex) == 0 && intData(prevClockIndex) > 0
  }

  def makeAsyncRegisterUpdate(registerIn: Symbol, registerOut: Symbol, clock: Symbol,
                              reset: ExpressionResult, init: ExpressionResult, info: Info): Unit = {
    val prevClockSymbol = symbolTable(SymbolTable.makePreviousValue(clock))

    val clockValue     = dataStore.GetInt(clock.index)
    val prevClockValue = dataStore.GetInt(prevClockSymbol.index)
    val clockHigh   = GtInts(clockValue.apply _, GetIntConstant(0).apply _)
    val clockWasLow = EqInts(prevClockValue.apply _, GetIntConstant(0).apply _)
    val isPosEdge   = AndInts(clockHigh.apply _, clockWasLow.apply _, 1)

    val posEdgeMux = processMux(isPosEdge, makeGet(registerIn), makeGet(registerOut))

    val resetValue = reset match {
      case i: IntExpressionResult => i
      case _ =>
        throw TreadleException(s"reset expression at $info, was not UInt<1>")
    }
    val asyncResetCondition = GtInts(resetValue.apply _, GetIntConstant(0).apply _)
    val asyncResetMux = processMux(asyncResetCondition, init, posEdgeMux)

    makeAssigner(registerOut, asyncResetMux, info = info)
  }

  //scalastyle:off cyclomatic.complexity method.length
  def makeAssigner(
    symbol                : Symbol,
    expressionResult      : ExpressionResult,
    conditionalClockSymbol: Option[Symbol] = None,
    info                  : Info
  ): Unit = {
    val assigner = (symbol.dataSize, expressionResult) match {
      case (IntSize,  result: IntExpressionResult)  =>
        dataStore.AssignInt(symbol, result.apply _, info)

      case (IntSize,  result: LongExpressionResult) =>
          dataStore.AssignInt(symbol,  ToInt(result.apply _).apply _, info)

      case (IntSize,  result: BigExpressionResult)  =>
          dataStore.AssignInt(symbol,  ToInt(result.apply _).apply _, info)

      case (LongSize, result: IntExpressionResult)  => dataStore.AssignLong(symbol, ToLong(result.apply _).apply _, info)
      case (LongSize, result: LongExpressionResult) => dataStore.AssignLong(symbol, result.apply _, info)
      case (LongSize, result: BigExpressionResult)  => dataStore.AssignLong(symbol, BigToLong(result.apply _).apply _, info)
      case (BigSize,  result: IntExpressionResult)  => dataStore.AssignBig(symbol,  ToBig(result.apply _).apply _, info)
      case (BigSize,  result: LongExpressionResult) => dataStore.AssignBig(symbol,  LongToBig(result.apply _).apply _, info)
      case (BigSize,  result: BigExpressionResult)  => dataStore.AssignBig(symbol,  result.apply _, info)
      case (size, result) =>
        val expressionSize = result match {
          case _: IntExpressionResult => "Int"
          case _: LongExpressionResult => "Long"
          case _: BigExpressionResult => "Big"
        }

        throw TreadleException(
          s"Error:assignment size mismatch ($size)${symbol.name} <= ($expressionSize)$expressionResult")
    }

    conditionalClockSymbol match {
      case Some(clockSymbol) =>
        val prevClockSymbol = symbolTable(SymbolTable.makePreviousValue(clockSymbol))
        val getter = ClockTransitionGetter(clockSymbol, prevClockSymbol)
        addAssigner(ClockBasedAssigner(assigner, getter, PositiveEdge))
      case _ =>
        addAssigner(assigner)
    }
  }


  def makeIndirectAssigner(
    portSymbol       : Symbol,
    memorySymbol     : Symbol,
    addr             : Symbol,
    enable           : Symbol,
    expressionResult : ExpressionResult,
    clock            : Symbol,
    info             : Info
  ): Unit = {

    def getIndex = dataStore.GetInt(addr.index).apply _
    def getEnable = {
      dataStore.GetInt(enable.index).apply _
    }

    val assigner = (memorySymbol.dataSize, expressionResult) match {
      case (IntSize, result: IntExpressionResult) =>
        dataStore.AssignIntIndirect(portSymbol, memorySymbol, getIndex, getEnable, result.apply _, info)
      case (LongSize, result: IntExpressionResult) =>
        dataStore.AssignLongIndirect(portSymbol, memorySymbol, getIndex, getEnable, ToLong(result.apply _).apply _, info)
      case (LongSize, result: LongExpressionResult) =>
        dataStore.AssignLongIndirect(portSymbol, memorySymbol, getIndex, getEnable, result.apply _, info)
      case (BigSize, result: IntExpressionResult) =>
        dataStore.AssignBigIndirect(portSymbol, memorySymbol, getIndex, getEnable, ToBig(result.apply _).apply _, info)
      case (BigSize, result: LongExpressionResult) =>
        dataStore.AssignBigIndirect(portSymbol, memorySymbol, getIndex, getEnable, LongToBig(result.apply _).apply _, info)
      case (BigSize, result: BigExpressionResult) =>
        dataStore.AssignBigIndirect(portSymbol, memorySymbol, getIndex, getEnable, result.apply _, info)
      case (size, result) =>
        val expressionSize = result match {
          case _: IntExpressionResult => "Int"
          case _: LongExpressionResult => "Long"
          case _: BigExpressionResult => "Big"
        }

        throw TreadleException(
          s"Error:assignment size mismatch ($size)${memorySymbol.name} <= ($expressionSize)$expressionResult")
    }
    addAssigner(assigner)
  }

  // this function is used by the memory compiler to combine some boolean signals
  def makeAnd(e1: ExpressionResult, e2: ExpressionResult, resultWidth: Int): ExpressionResult = (e1, e2) match {
    case (a: IntExpressionResult, b: IntExpressionResult) => {
      AndInts(a.apply _, b.apply _, resultWidth)
    }
    case _=> throw new RuntimeException("makeAnd only implemented for Int & Int!")
  }

  def processPrintf(printf: Statement, enable: ExpressionResult, args: Seq[ExpressionResult]):
  (PrintfConditionResult, Seq[PrintfArgExpressionResult]) = {
    val intExpression = enable match {
      case i : IntExpressionResult  => i
      case l : LongExpressionResult => LongToInt(l.apply _)
      case b : BigExpressionResult  => ToInt(b.apply _)
      case _ =>
        throw TreadleException(s"Error: printf $printf has unknown condition type")
    }
    val boolExpression = new PrintfConditionResult {
      override def apply() = intExpression.apply() > 0
    }

    def argExpr(e: ExpressionResult) : PrintfArgExpressionResult = e match {
      case i : IntExpressionResult  => PrintfArgExpressionResult(i.apply _)
      case l : LongExpressionResult => PrintfArgExpressionResult(l.apply _)
      case b : BigExpressionResult  => PrintfArgExpressionResult(b.apply _)
      case _ =>
        throw TreadleException(s"Error: printf $printf has unknown condition type")
    }

    (boolExpression, args.map(argExpr))
  }

  override def processStop(stop: Statement, enable: ExpressionResult): StopConditionResult = {
    val intExpression = enable match {
      case i : IntExpressionResult  => i
      case l : LongExpressionResult => LongToInt(l.apply _)
      case b : BigExpressionResult  => ToInt(b.apply _)
      case _ =>
        throw TreadleException(s"Error: stop $stop has unknown condition type")
    }
    val boolExpression = new StopConditionResult {
      override def apply() = intExpression.apply() > 0
    }
    boolExpression
  }

  def makePrevClockAssigner(clock: Symbol, prevClock: Symbol) : Assigner = {
    dataStore.AssignInt(prevClock, makeGet(clock).asInstanceOf[IntExpressionResult].apply _, info = NoInfo)
  }
}

class ExpressionCompiler(expand: String => String, compiler: Compiler, validIfIsRandom: Boolean)
  extends treadle.executable.ExpressionCompiler(expand, compiler.processMux) {


  def binaryOps(opCode: PrimOp, args: Seq[Expression], tpe: Type): ExpressionResult = {

    def getParameters(e: Expression) = (processExpression(e), getSigned(e), getWidth(e))

    val (arg1, _, arg1Width) = getParameters(args.head)
    val (arg2, _, arg2Width) = getParameters(args.tail.head)

    def handleIntResult(e1: IntExpressionResult, e2: IntExpressionResult): ExpressionResult = {
      opCode match {
        case Add => AddInts(e1.apply _, e2.apply _)
        case Sub => SubInts(e1.apply _, e2.apply _)
        case Mul => MulInts(e1.apply _, e2.apply _)
        case Div => DivInts(e1.apply _, e2.apply _)
        case Rem => RemInts(e1.apply _, e2.apply _)

        case Eq  => EqInts(e1.apply _,  e2.apply _)
        case Neq => NeqInts(e1.apply _, e2.apply _)
        case Lt  => LtInts(e1.apply _,  e2.apply _)
        case Leq => LeqInts(e1.apply _, e2.apply _)
        case Gt  => GtInts(e1.apply _,  e2.apply _)
        case Geq => GeqInts(e1.apply _, e2.apply _)

        case Dshl => DshlInts(e1.apply _, e2.apply _)
        case Dshr => DshrInts(e1.apply _, e2.apply _)

        case And => AndInts(e1.apply _, e2.apply _, arg1Width.max(arg2Width))
        case Or  => OrInts(e1.apply _,  e2.apply _, arg1Width.max(arg2Width))
        case Xor => XorInts(e1.apply _, e2.apply _, arg1Width.max(arg2Width))

        case Cat =>
          CatInts(e1.apply _, arg1Width, e2.apply _, arg2Width)

        case _ =>
          throw TreadleException(s"Error:BinaryOp:$opCode)(${args.head}, ${args.tail.head})")
      }
    }

    def handleLongResult(e1: LongExpressionResult, e2: LongExpressionResult): ExpressionResult = {
      opCode match {
        case Add => AddLongs(e1.apply _, e2.apply _)
        case Sub => SubLongs(e1.apply _, e2.apply _)
        case Mul => MulLongs(e1.apply _, e2.apply _)
        case Div => DivLongs(e1.apply _, e2.apply _)
        case Rem => RemLongs(e1.apply _, e2.apply _)

        case Eq  => EqLongs(e1.apply _, e2.apply _)
        case Neq => NeqLongs(e1.apply _, e2.apply _)
        case Lt  => LtLongs(e1.apply _, e2.apply _)
        case Leq => LeqLongs(e1.apply _, e2.apply _)
        case Gt  => GtLongs(e1.apply _, e2.apply _)
        case Geq => GeqLongs(e1.apply _, e2.apply _)

        case Dshl => DshlLongs(e1.apply _, e2.apply _)
        case Dshr => DshrLongs(e1.apply _, e2.apply _)

        case And  => AndLongs(e1.apply _, e2.apply _, arg1Width.max(arg2Width))
        case Or   => OrLongs(e1.apply _, e2.apply _, arg1Width.max(arg2Width))
        case Xor  => XorLongs(e1.apply _, e2.apply _, arg1Width.max(arg2Width))

        case Cat =>
          CatLongs(e1.apply _, arg1Width, e2.apply _, arg2Width)

        case _ =>
          throw TreadleException(s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head})")
      }
    }

    def handleBigResult(e1: BigExpressionResult, e2: BigExpressionResult): ExpressionResult = {
      opCode match {
        case Add => AddBigs(e1.apply _, e2.apply _)
        case Sub => SubBigs(e1.apply _, e2.apply _)
        case Mul => MulBigs(e1.apply _, e2.apply _)
        case Div => DivBigs(e1.apply _, e2.apply _)
        case Rem => RemBigs(e1.apply _, e2.apply _)

        case Eq  => EqBigs(e1.apply _, e2.apply _)
        case Neq => NeqBigs(e1.apply _, e2.apply _)
        case Lt  => LtBigs(e1.apply _, e2.apply _)
        case Leq => LeqBigs(e1.apply _, e2.apply _)
        case Gt  => GtBigs(e1.apply _, e2.apply _)
        case Geq => GeqBigs(e1.apply _, e2.apply _)

        case Dshl => DshlBigs(e1.apply _, e2.apply _)
        case Dshr => DshrBigs(e1.apply _, e2.apply _)

        case And  => AndBigs(e1.apply _, e2.apply _, arg1Width.max(arg2Width))
        case Or   => OrBigs(e1.apply _, e2.apply _, arg1Width.max(arg2Width))
        case Xor  => XorBigs(e1.apply _, e2.apply _, arg1Width.max(arg2Width))

        case Cat =>
          CatBigs(e1.apply _, arg1Width, e2.apply _, arg2Width)

        case _ =>
          throw TreadleException(s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head})")
      }
    }

    (DataSize(getWidth(tpe)), arg1, arg2) match {

      case (IntSize,  e1: IntExpressionResult, e2: IntExpressionResult) =>
        handleIntResult(e1, e2)

      case (IntSize, e1: LongExpressionResult, e2: IntExpressionResult) =>
        handleLongResult(e1, ToLong(e2.apply _))
      case (IntSize, e1: BigExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(e1, ToBig(e2.apply _))

      case (IntSize, e1: IntExpressionResult, e2: LongExpressionResult) =>
        handleLongResult(ToLong(e1.apply _), e2)
      case (IntSize, e1: LongExpressionResult, e2: LongExpressionResult) =>
        handleLongResult(e1, e2)
      case (IntSize, e1: BigExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(e1, LongToBig(e2.apply _))

      case (IntSize, e1: IntExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(ToBig(e1.apply _), e2)
      case (IntSize, e1: LongExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(LongToBig(e1.apply _), e2)
      case (IntSize, e1: BigExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(e1, e2)
      case (IntSize, _, _) =>
        throw TreadleException(
          s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head}) ($arg1, $arg2)")

      case (LongSize, e1: IntExpressionResult, e2: IntExpressionResult) =>
        handleLongResult(ToLong(e1.apply _), ToLong(e2.apply _))
      case (LongSize, e1: LongExpressionResult, e2: IntExpressionResult) =>
        handleLongResult(e1, ToLong(e2.apply _))
      case (LongSize, e1: BigExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(e1, ToBig(e2.apply _))

      case (LongSize, e1: IntExpressionResult, e2: LongExpressionResult) =>
        handleLongResult(ToLong(e1.apply _), e2)
      case (LongSize, e1: LongExpressionResult, e2: LongExpressionResult) =>
        handleLongResult(e1, e2)
      case (LongSize, e1: BigExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(e1, LongToBig(e2.apply _))

      case (LongSize, e1: IntExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(ToBig(e1.apply _), e2)
      case (LongSize, e1: LongExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(LongToBig(e1.apply _), e2)
      case (LongSize, e1: BigExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(e1, e2)
      case (LongSize, _, _) =>
        throw TreadleException(
          s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head}) ($arg1, $arg2)")

      case (BigSize, e1: IntExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(ToBig(e1.apply _), ToBig(e2.apply _))
      case (BigSize, e1: LongExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(LongToBig(e1.apply _), ToBig(e2.apply _))
      case (BigSize, e1: BigExpressionResult, e2: IntExpressionResult) =>
        handleBigResult(e1, ToBig(e2.apply _))

      case (BigSize, e1: IntExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(ToBig(e1.apply _), LongToBig(e2.apply _))
      case (BigSize, e1: LongExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(LongToBig(e1.apply _), LongToBig(e2.apply _))
      case (BigSize, e1: BigExpressionResult, e2: LongExpressionResult) =>
        handleBigResult(e1, LongToBig(e2.apply _))

      case (BigSize, e1: IntExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(ToBig(e1.apply _), e2)
      case (BigSize, e1: LongExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(LongToBig(e1.apply _), e2)
      case (BigSize, e1: BigExpressionResult, e2: BigExpressionResult) =>
        handleBigResult(e1, e2)

      case (BigSize, _, _) =>
        throw TreadleException(
          s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head}) ($arg1, $arg2)")

      case (_, _, _) =>
        throw TreadleException(
          s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head}) ($arg1, $arg2)")
    }
  }

  def oneArgOneParamOps(
                         op: PrimOp,
                         expressions: Seq[Expression],
                         ints: Seq[BigInt],
                         tpe: firrtl.ir.Type
                       ): ExpressionResult = {
    val arg1 = processExpression(expressions.head)
    val arg1Width = getWidth(expressions.head)
    val param1 = ints.head.toInt

    arg1 match {
      case e1: IntExpressionResult =>
        op match {
          case Head => HeadInts(e1.apply _, takeBits = param1, arg1Width)
          case Tail => TailInts(e1.apply _, toDrop = param1, arg1Width)
          case Shl  => ShlInts(e1.apply _, GetIntConstant(param1).apply _)
          case Shr  => ShrInts(e1.apply _, GetIntConstant(param1).apply _)
        }
      case e1: LongExpressionResult =>
        op match {
          case Head => HeadLongs(e1.apply _, takeBits = param1, arg1Width)
          case Tail => TailLongs(e1.apply _, toDrop = param1, arg1Width)
          case Shl  => ShlLongs(e1.apply _, GetLongConstant(param1).apply _)
          case Shr  => ShrLongs(e1.apply _, GetLongConstant(param1).apply _)
        }
      case e1: BigExpressionResult =>
        op match {
          case Head => HeadBigs(e1.apply _, takeBits = param1, arg1Width)
          case Tail => TailBigs(e1.apply _, toDrop = param1, arg1Width)
          case Shl  => ShlBigs(e1.apply _, GetBigConstant(param1).apply _)
          case Shr  => ShrBigs(e1.apply _, GetBigConstant(param1).apply _)
        }
    }
  }

  def oneArgTwoParamOps(
                         op: PrimOp,
                         expressions: Seq[Expression],
                         ints: Seq[BigInt],
                         tpe: firrtl.ir.Type
                       ): ExpressionResult = {
    val arg1 = processExpression(expressions.head)
    val arg2 = ints.head
    val arg3 = ints.tail.head
    val width = tpe match {
      case UIntType(IntWidth(n)) => n.toInt
      case SIntType(IntWidth(n)) => n.toInt
    }

    arg1 match {
      case e1: IntExpressionResult =>
        op match {
          case Bits => BitsInts(e1.apply _, arg2.toInt, arg3.toInt, width)
        }
      case e1: LongExpressionResult =>
        op match {
          case Bits => BitsLongs(e1.apply _, arg2.toInt, arg3.toInt, width)
        }
      case e1: BigExpressionResult =>
        op match {
          case Bits => BitsBigs(e1.apply _, arg2.toInt, arg3.toInt, width)
        }
    }
  }

  def unaryOps(
                op: PrimOp,
                expressions: Seq[Expression],
                tpe: firrtl.ir.Type
              ): ExpressionResult = {
    val arg1 = processExpression(expressions.head)

    val width = tpe match {
      case UIntType(IntWidth(n)) => n.toInt
      case SIntType(IntWidth(n)) => n.toInt
      case ClockType             => 1
      case AsyncResetType        => 1
    }

    val sourceWidth = getWidth(expressions.head)

    arg1 match {
      case e1: IntExpressionResult =>
        op match {
          case Pad            => e1
          case AsUInt         => AsUIntInts(e1.apply _, width)
          case AsSInt         => AsSIntInts(e1.apply _, width)
          case AsClock        => e1
          case AsAsyncReset   => e1

          case Cvt            => e1
          case Neg            => NegInts(e1.apply _)
          case Not            => NotInts(e1.apply _, width)

          case Andr           => AndrInts(e1.apply _, sourceWidth)
          case Orr            => OrrInts(e1.apply _,  sourceWidth)
          case Xorr           => XorrInts(e1.apply _, sourceWidth)
        }
      case e1: LongExpressionResult =>
        op match {
          case Pad            => e1
          case AsUInt         => AsUIntLongs(e1.apply _, width)
          case AsSInt         => AsSIntLongs(e1.apply _, width)
          case AsClock        => e1
          case AsAsyncReset   => e1

          case Cvt            => e1
          case Neg            => NegLongs(e1.apply _)
          case Not            => NotLongs(e1.apply _, width)

          case Andr           => AndrLongs(e1.apply _, sourceWidth)
          case Orr            => OrrLongs(e1.apply _,  sourceWidth)
          case Xorr           => XorrLongs(e1.apply _, sourceWidth)
        }
      case e1: BigExpressionResult =>
        op match {
          case Pad            => e1
          case AsUInt         => AsUIntBigs(e1.apply _, width)
          case AsSInt         => AsSIntBigs(e1.apply _, width)
          case AsClock        => e1
          case AsAsyncReset   => e1

          case Cvt            => e1
          case Neg            => NegBigs(e1.apply _)
          case Not            => NotBigs(e1.apply _, width)

          case Andr           => AndrBigs(e1.apply _, sourceWidth)
          case Orr            => OrrBigs(e1.apply _,  sourceWidth)
          case Xorr           => XorrBigs(e1.apply _, sourceWidth)
        }
    }
  }

  def validIf(condition: ExpressionResult, value: ExpressionResult, resultWidth: Int): ExpressionResult = {
    if(validIfIsRandom) {
      condition match {
        case c: IntExpressionResult =>
          value match {
            case t: IntExpressionResult =>
              MuxInts(c.apply _, t.apply _, UndefinedInts(resultWidth).apply _)
            case t: LongExpressionResult =>
              MuxLongs(c.apply _, t.apply _, UndefinedLongs(resultWidth).apply _)
            case t: BigExpressionResult =>
              MuxBigs(c.apply _, t.apply _, UndefinedBigs(resultWidth).apply _)
            case _ =>
              throw TreadleException(s"Mux condition is not 1 bit $condition parsed as $c")
          }
        case c =>
          throw TreadleException(s"Mux condition is not 1 bit $condition parsed as $c")
      }
    }
    else {
      value
    }
  }

  def makeGet(sourceName: String): ExpressionResult = compiler.makeGet(compiler.symbolTable(sourceName))

  def literal(value: Big, width: Big, signed: Boolean): ExpressionResult = {
    DataSize(width) match {
      case IntSize  => GetIntConstant(value.toInt)
      case LongSize => GetLongConstant(value.toLong)
      case BigSize  => GetBigConstant(value)
    }
  }
}