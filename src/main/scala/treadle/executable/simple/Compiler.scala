// See LICENSE for license details.

package treadle.executable.simple

import firrtl.PrimOps._
import firrtl.ir._
import treadle.ScalaBlackBoxFactory
import treadle.executable._

class Compiler(
    val symbolTable  : SymbolTable,
    private val dataStore : DataStore,
    scheduler        : Scheduler,
    validIfIsRandom  : Boolean,
    blackBoxFactories: Seq[ScalaBlackBoxFactory]
  ) extends BaseCompiler(symbolTable, dataStore, scheduler) with FirrtlHelpers {

  def getExpressionCompiler(expand: String => String): treadle.executable.ExpressionCompiler = {
    new simple.ExpressionCompiler(expand, this, validIfIsRandom)
  }

  def makeGet(source: Symbol): ExpressionResult = dataStore.Get(source.index)

  def makeGetIndirect(memory: Symbol, data: Symbol, enable: Symbol, addr: Symbol): ExpressionResult = {
    dataStore.GetIndirect(memory, dataStore.Get(addr.index).apply _, dataStore.Get(enable.index).apply _)
  }

  private def asBig(e: ExpressionResult): FuncBig = {
    assert(e.isInstanceOf[BigExpressionResult], s"$e")
    e.asInstanceOf[BigExpressionResult].apply _
  }

  def processMux(condition: ExpressionResult, tru: ExpressionResult, fals: ExpressionResult): ExpressionResult = {
    MuxBigs(asBig(condition), asBig(tru), asBig(fals))
  }

  def makeClockTransitionGetter(clockSymbol: Symbol, prevClockSymbol: Symbol): AbstractClockTransitionGetter =
    ClockTransitionGetter(clockSymbol, prevClockSymbol)

  case class ClockTransitionGetter(clockSymbol: Symbol, prevClockSymbol: Symbol) extends AbstractClockTransitionGetter {
    def getClockSymbol: Symbol = clockSymbol
    def isPosEdge: Boolean = dataStore(clockSymbol) > 0  && dataStore(prevClockSymbol) == 0
    def isNegEdge: Boolean = dataStore(clockSymbol) == 0 && dataStore(prevClockSymbol) > 0
  }

  def makeAsyncRegisterUpdate(registerIn: Symbol, registerOut: Symbol, clock: Symbol,
                              reset: ExpressionResult, init: ExpressionResult, info: Info): Unit = {
    val prevClockSymbol = symbolTable(SymbolTable.makePreviousValue(clock))

    val clockValue     = dataStore.Get(clock.index)
    val prevClockValue = dataStore.Get(prevClockSymbol.index)
    val clockHigh   = GtBigs(clockValue.apply _, GetBigConstant(0).apply _)
    val clockWasLow = EqBigs(prevClockValue.apply _, GetBigConstant(0).apply _)
    val isPosEdge   = AndBigs(clockHigh.apply _, clockWasLow.apply _, 1)

    val posEdgeMux = processMux(isPosEdge, makeGet(registerIn), makeGet(registerOut))

    val asyncResetCondition = GtBigs(asBig(reset), GetBigConstant(0).apply _)
    val asyncResetMux = processMux(asyncResetCondition, init, posEdgeMux)

    makeAssigner(registerOut, asyncResetMux, info = info)
  }

  def makeAssigner(symbol: Symbol, expressionResult: ExpressionResult,
                   conditionalClockSymbol: Option[Symbol] = None, info: Info): Unit = {
    val baseAssigner = dataStore.Assign(symbol, asBig(expressionResult), info)
    val assigner = conditionalClockSymbol match {
      case Some(clock) =>
        val prevClock = symbolTable(SymbolTable.makePreviousValue(clock))
        val getter = ClockTransitionGetter(clock, prevClock)
        ClockBasedAssigner(baseAssigner, getter, PositiveEdge)
      case None => baseAssigner
    }
    addAssigner(assigner) // TODO: move this out of the function
  }

  def makeIndirectAssigner(port: Symbol, memory: Symbol, addr: Symbol, enable: Symbol, result : ExpressionResult,
                           clock: Symbol, info: Info): Unit = {
    val getIndex = dataStore.Get(addr.index).apply _
    val getEnable = dataStore.Get(enable.index).apply _
    val assigner = dataStore.AssignIndirect(port, memory, getIndex, getEnable, asBig(result), info)
    addAssigner(assigner) // TODO: move this out of the function
  }

  def makeAnd(e1: ExpressionResult, e2: ExpressionResult, resultWidth: Int): ExpressionResult = {
    AndBigs(asBig(e1), asBig(e2), resultWidth)
  }

  def processPrintf(printf: Statement, enable: ExpressionResult, args: Seq[ExpressionResult]):
  (PrintfConditionResult, Seq[PrintfArgExpressionResult]) = {
    val cond = new PrintfConditionResult {
      override def apply() = asBig(enable).apply() > 0
    }
    val bigArgs = args.map{ e => PrintfArgExpressionResult(asBig(e).apply _) }
    (cond, bigArgs)
  }

  override def processStop(stop: Statement, enable: ExpressionResult): StopConditionResult = {
    val cond = new StopConditionResult {
      override def apply() = asBig(enable).apply() > 0
    }
    cond
  }

  def makePrevClockAssigner(clock: Symbol, prevClock: Symbol) : Assigner = {
    dataStore.Assign(prevClock, dataStore.Get(clock.index).apply _, info = NoInfo)
  }
}


class ExpressionCompiler(expand: String => String, compiler: Compiler, validIfIsRandom: Boolean)
    extends treadle.executable.ExpressionCompiler(expand, compiler.processMux) {

  private def asBig(e: ExpressionResult): BigExpressionResult = {
    assert(e.isInstanceOf[BigExpressionResult], s"$e")
    e.asInstanceOf[BigExpressionResult]
  }

  override def processExpression(expression: Expression) : BigExpressionResult = {
    asBig(super.processExpression(expression))
  }

  private def processArg(e: Expression) : (BigExpressionResult, Big) = (processExpression(e), getWidth(e))

  //scalastyle:off cyclomatic.complexity method.length
  def binaryOps(opCode: PrimOp, args: Seq[Expression], tpe: Type): ExpressionResult = {
    val (e1, arg1Width) = processArg(args.head)
    val (e2, arg2Width) = processArg(args(1))

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

      case And  => AndBigs(e1.apply _, e2.apply _, arg1Width.max(arg2Width).toInt)
      case Or   => OrBigs(e1.apply _, e2.apply _, arg1Width.max(arg2Width).toInt)
      case Xor  => XorBigs(e1.apply _, e2.apply _, arg1Width.max(arg2Width).toInt)

      case Cat => CatBigs(e1.apply _, arg1Width.toInt, e2.apply _, arg2Width.toInt)

      case _ =>
        throw TreadleException(s"Error:BinaryOp:$opCode(${args.head}, ${args.tail.head})")
    }
  }

  def oneArgOneParamOps(op: PrimOp, expressions: Seq[Expression], ints: Seq[BigInt], tpe: Type): ExpressionResult = {
    val (e1, arg1Width) = processArg(expressions.head)
    val param1 = ints.head
    op match {
      case Head => HeadBigs(e1.apply _, takeBits = param1.toInt, arg1Width.toInt)
      case Tail => TailBigs(e1.apply _, toDrop = param1.toInt, arg1Width.toInt)
      case Shl  => ShlBigs(e1.apply _, GetBigConstant(param1).apply _)
      case Shr  => ShrBigs(e1.apply _, GetBigConstant(param1).apply _)
    }
  }

  def oneArgTwoParamOps(op: PrimOp, expressions: Seq[Expression], ints: Seq[BigInt], tpe: Type): ExpressionResult = {
    val (e1, width) = (processExpression(expressions.head), getWidth(tpe))
    assert(op == Bits)
    BitsBigs(e1.apply _, ints.head.toInt, ints(1).toInt, width.toInt)
  }

  def unaryOps(op: PrimOp, expressions: Seq[Expression], tpe: Type): ExpressionResult = {
    val (e1, sourceWidth) = processArg(expressions.head)
    val width = getWidth(tpe)
    op match {
      case Pad            => e1
      case AsUInt         => AsUIntBigs(e1.apply _, width)
      case AsSInt         => AsSIntBigs(e1.apply _, width)
      case AsClock        => e1
      case AsAsyncReset   => e1

      case Cvt            => e1
      case Neg            => NegBigs(e1.apply _)
      case Not            => NotBigs(e1.apply _, width)

      case Andr           => AndrBigs(e1.apply _, sourceWidth.toInt)
      case Orr            => OrrBigs(e1.apply _,  sourceWidth.toInt)
      case Xorr           => XorrBigs(e1.apply _, sourceWidth.toInt)
    }
  }

  def validIf(condition: ExpressionResult, value: ExpressionResult, resultWidth: Int): ExpressionResult = {
    if(validIfIsRandom) {
      MuxBigs(asBig(condition).apply _, asBig(value).apply _, UndefinedBigs(resultWidth).apply _)
    } else { value }
  }

  def makeGet(sourceName: String): ExpressionResult = compiler.makeGet(compiler.symbolTable(sourceName))

  def literal(value: Big, width: Big, signed: Boolean): ExpressionResult = GetBigConstant(value)
}