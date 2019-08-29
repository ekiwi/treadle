// See LICENSE for license details.

package treadle.executable

import firrtl.PrimOps._
import firrtl._
import firrtl.ir._
import treadle._
import treadle.utils.FindModule

import scala.collection.mutable

trait AbstractCompiler {
  def compile(circuit: Circuit, blackBoxFactories: Seq[ScalaBlackBoxFactory]): Unit
  def makeGet(source: Symbol): ExpressionResult
  def makeGetIndirect(memory: Symbol, data: Symbol, enable: Symbol, addr: Symbol): ExpressionResult
  def makeAssigner(symbol: Symbol, expressionResult: ExpressionResult, conditionalClockSymbol: Option[Symbol] = None,
                   info: Info)
  def makeIndirectAssigner(portSymbol: Symbol, memorySymbol: Symbol, addr: Symbol, enable: Symbol,
                           expressionResult: ExpressionResult, clock: Symbol, info: Info)
  def makeAnd(e1: ExpressionResult, e2: ExpressionResult, resultWidth: Int): ExpressionResult
}


trait FirrtlHelpers {
  def getWidth(tpe: firrtl.ir.Type): Int = {
    tpe match {
      case GroundType(IntWidth(width)) => width.toInt
      case _ => throw TreadleException(s"Unresolved width found in firrtl.ir.Type $tpe")
    }
  }

  def getWidth(expression: Expression): Int = {
    expression.tpe match {
      case GroundType(IntWidth(width)) => width.toInt
      case _ =>
        throw TreadleException(
          s"Unresolved width found in expression $expression of firrtl.ir.Type ${expression.tpe}")
    }
  }

  def getSigned(expression: Expression): Boolean = {
    expression.tpe match {
      case  _: UIntType    => false
      case  _: SIntType    => true
      case  ClockType      => false
      case _ =>
        throw TreadleException(
          s"Unsupported type found in expression $expression of firrtl.ir.Type ${expression.tpe}")
    }
  }

}

case class ExternalModuleInputAssigner(
    symbol:             Symbol,
    readValue:          () => Big,
    portName:           String,
    blackBox:           ScalaBlackBox,
    underlyingAssigner: Assigner
  ) extends Assigner {
  val info: Info = underlyingAssigner.info
  override def run: FuncUnit = {
    underlyingAssigner.run()
    blackBox.inputChanged(portName, readValue())
    () => Unit
  }
}

case class BlackBoxShim(unexpandedName: String, output: Symbol, inputs: Seq[Symbol], box: ScalaBlackBox,
                        dataStore: AbstractDataStore) extends BigExpressionResult {
  def apply(): Big = {
    val inputValues = inputs.map { input => dataStore(input) }
    val bigInt = box.getOutput(inputValues, output.firrtlType, unexpandedName)
    bigInt
  }
}


abstract class ExpressionCompiler(
 expand: String => String,
 processMux: (ExpressionResult, ExpressionResult, ExpressionResult) => ExpressionResult
 ) extends FirrtlHelpers {
  def binaryOps(opCode: PrimOp, args: Seq[Expression], tpe: Type): ExpressionResult
  def oneArgOneParamOps(op: PrimOp, expressions: Seq[Expression], ints: Seq[BigInt], tpe: Type): ExpressionResult
  def oneArgTwoParamOps(op: PrimOp, expressions: Seq[Expression], ints: Seq[BigInt], tpe: Type): ExpressionResult
  def unaryOps(op: PrimOp, expressions: Seq[Expression], tpe: Type): ExpressionResult
  def validIf(condition: ExpressionResult, value: ExpressionResult, resultType: Type): ExpressionResult
  def makeGet(sourceName: String): ExpressionResult
  def literal(value: Big, width: Big, signed: Boolean): ExpressionResult

  //scalastyle:off cyclomatic.complexity method.length
  def processExpression(expression: Expression): ExpressionResult = {
    val result: ExpressionResult = expression match {
      case Mux(condition, trueExpression, falseExpression, _) =>
        processMux(
          processExpression(condition),
          processExpression(trueExpression),
          processExpression(falseExpression)
        )
      case WRef(name, _, _, _) =>
        makeGet(expand(name))
      case subfield: WSubField =>
        makeGet(expand(subfield.serialize))
      case subIndex: WSubIndex =>
        makeGet(expand(subIndex.serialize))

      case ValidIf(condition, value, tpe) =>
        validIf(processExpression(condition), processExpression(value), tpe)

      case DoPrim(op, args, const, tpe) =>
        val v = op match {
          case Add => binaryOps(op, args, tpe)
          case Sub => binaryOps(op, args, tpe)
          case Mul => binaryOps(op, args, tpe)
          case Div => binaryOps(op, args, tpe)
          case Rem => binaryOps(op, args, tpe)

          case Eq  => binaryOps(op, args, tpe)
          case Neq => binaryOps(op, args, tpe)
          case Lt  => binaryOps(op, args, tpe)
          case Leq => binaryOps(op, args, tpe)
          case Gt  => binaryOps(op, args, tpe)
          case Geq => binaryOps(op, args, tpe)

          case Pad     => oneArgOneParamOps(op, args, const, tpe)

          case AsUInt       => unaryOps(op, args, tpe)
          case AsSInt       => unaryOps(op, args, tpe)
          case AsClock      => unaryOps(op, args, tpe)
          case AsAsyncReset => unaryOps(op, args, tpe)

          case Shl => oneArgOneParamOps(op, args, const, tpe)
          case Shr => oneArgOneParamOps(op, args, const, tpe)

          case Dshl => binaryOps(op, args, tpe)
          case Dshr => binaryOps(op, args, tpe)

          case Cvt => unaryOps(op, args, tpe)
          case Neg => unaryOps(op, args, tpe)
          case Not => unaryOps(op, args, tpe)

          case And => binaryOps(op, args, tpe)
          case Or  => binaryOps(op, args, tpe)
          case Xor => binaryOps(op, args, tpe)

          case Andr => unaryOps(op, args, tpe)
          case Orr =>  unaryOps(op, args, tpe)
          case Xorr => unaryOps(op, args, tpe)

          case Cat => binaryOps(op, args, tpe)

          case Bits => oneArgTwoParamOps(op, args, const, tpe)

          case Head => oneArgOneParamOps(op, args, const, tpe)
          case Tail => oneArgOneParamOps(op, args, const, tpe)

          case _ =>
            throw new Exception(s"processExpression:error: unhandled expression $expression")
        }
        v
      case UIntLiteral(value, IntWidth(width)) =>
        literal(value, width, signed=false)
      case SIntLiteral(value, IntWidth(width)) =>
        literal(value, width, signed=true)
      case _ =>
        throw TreadleException(s"bad expression $expression")
    }
    result
  }
}



abstract class BaseCompiler(symbolTable: SymbolTable, dataStore: AbstractDataStore, scheduler: Scheduler)
    extends AbstractCompiler with logger.LazyLogging  {
  case class ExternalInputParams(instance: ScalaBlackBox, portName: String)
  private val externalModuleInputs = new mutable.HashMap[Symbol, ExternalInputParams]

  def addAssigner(assigner: Assigner): Unit = {
    val symbol = assigner.symbol
    externalModuleInputs.get(symbol) match {
      case Some(ExternalInputParams(instance, portName)) =>
        // if there's a black box listening to this add the ext module wrapper
        val readValue = () => dataStore(symbol)
        scheduler.addAssigner(symbol, ExternalModuleInputAssigner(symbol, readValue, portName, instance, assigner))
      case _ =>
        // typical case
        scheduler.addAssigner(symbol, assigner)
    }
  }

  def getExpressionCompiler(expand: String => String): ExpressionCompiler

  def processMux(condition: ExpressionResult, trueExpression: ExpressionResult, falseExpression: ExpressionResult): ExpressionResult

  def processPrintf(printf: Statement, enable: ExpressionResult, args: Seq[ExpressionResult]):
  (PrintfConditionResult, Seq[PrintfArgExpressionResult])
  def processStop(stop: Statement, enable: ExpressionResult): StopConditionResult
  def makeClockTransitionGetter(clockSymbol: Symbol, prevClockSymbol: Symbol): AbstractClockTransitionGetter
  def makeAsyncRegisterUpdate(registerIn: Symbol, registerOut: Symbol, clock: Symbol,
                              reset: ExpressionResult, init: ExpressionResult, info: Info): Unit
  //scalastyle:off cyclomatic.complexity method.length
  def processStatements(modulePrefix: String, circuit: Circuit, statement: firrtl.ir.Statement): Unit = {
    def expand(name: String): String = if(modulePrefix.isEmpty) name else modulePrefix + "." + name
    val exprCompiler = getExpressionCompiler(expand)

    def getDrivingClock(clockExpression: Expression): Option[Symbol] = {

      clockExpression match {
        case WRef(clockName, _, _, _) =>
          for {
            clockSym <- symbolTable.get(expand(clockName))
            topClock <- symbolTable.findHighestClock(clockSym)
          } yield {
            topClock
          }
        case DoPrim(AsClock, Seq(arg), _, _) => getDrivingClock(arg)
        case _ =>
          None
      }
    }

    statement match {
      case block: Block =>
        var statementNumber = 0
        while(statementNumber < block.stmts.length) {
          processStatements(modulePrefix, circuit, block.stmts(statementNumber))
          statementNumber += 1
        }

      case con: Connect =>
        // if it's a register we use the name of its input side

        val expandedName = expand(con.loc.serialize)
        if(symbolTable.isRegister(expandedName)) {
          val registerIn  = symbolTable(SymbolTable.makeRegisterInputName(expandedName))

          val processedExpression = exprCompiler.processExpression(con.expr)

          makeAssigner(registerIn, processedExpression, info = con.info)
        }
        else {
          val assignedSymbol = symbolTable(expandedName)
          makeAssigner(assignedSymbol, exprCompiler.processExpression(con.expr), info = con.info)

          if(assignedSymbol.firrtlType == ClockType) {
            //
            // If we are here then we need to add an assigner at the end of the cycle that records
            // the clocks state in the clock's prev state
            //
            val prevClockSymbol = symbolTable(SymbolTable.makePreviousValue(assignedSymbol))
            val prevClockAssigner = makePrevClockAssigner(assignedSymbol, prevClockSymbol)
            scheduler.addEndOfCycleAssigner(prevClockAssigner)
          }
        }

      case WDefInstance(info, instanceName, moduleName, _) =>
        val subModule = FindModule(moduleName, circuit)
        val newPrefix = if(modulePrefix.isEmpty) instanceName else modulePrefix + "." + instanceName
        logger.debug(s"declaration:WDefInstance:$instanceName:$moduleName prefix now $newPrefix")
        processModule(newPrefix, subModule, circuit)

        subModule match {
          case extModule: ExtModule =>
            val instanceSymbol = symbolTable(expand(instanceName))

            symbolTable.getBlackboxImplementation(instanceSymbol) match {
              case Some(implementation) =>
                val instanceSymbol = symbolTable(expand(instanceName))

                implementation.setParams(extModule.params)

                for (port <- extModule.ports) {
                  if (port.direction == Output) {
                    val portSymbol = symbolTable(expand(instanceName + "." + port.name))
                    val inputSymbols = implementation.outputDependencies(port.name).map { inputName =>
                      symbolTable(expand(instanceName + "." + inputName))
                    }
                    val shim = BlackBoxShim(port.name, portSymbol, inputSymbols, implementation, dataStore)
                    makeAssigner(portSymbol, shim, info = info)
                  }
                  if (port.tpe == ClockType) {
                    val clockSymbol = symbolTable(expand(instanceName + "." + port.name))
                    val prevClockSymbol = symbolTable(SymbolTable.makePreviousValue(clockSymbol))

                    val clockTransitionGetter = makeClockTransitionGetter(clockSymbol, prevClockSymbol)

                    val blackBoxCycler = BlackBoxCycler(
                      instanceSymbol, implementation, clockSymbol, clockTransitionGetter, info)

                    val drivingClockOption = symbolTable.findHighestClock(clockSymbol)

                    scheduler.addAssigner(instanceSymbol, blackBoxCycler)
                  }
                  else if(port.direction == Input) {
                    val portSymbol = symbolTable(expand(instanceName + "." + port.name))
                    externalModuleInputs(portSymbol) = ExternalInputParams(implementation, port.name)
                  }
                }
              case _ =>
                println(
                  s"""WARNING: external module "${extModule.defname}"($modulePrefix:${extModule.name})""" +
                          """was not matched with an implementation""")
            }
          case _ =>
          // not external module, it was processed above
        }

      case DefNode(info, name, expression) =>
        val symbol = symbolTable(expand(name))
        logger.debug(s"declaration:DefNode:${symbol.name}:${expression.serialize}")
        makeAssigner(symbol, exprCompiler.processExpression(expression), info = info)
        if(symbol.firrtlType == ClockType) {
          //
          // If we are here then we need to add an assigner at the end of the cycle that records
          // the clocks state in the clock's prev state
          //
          val prevClockSymbol = symbolTable(SymbolTable.makePreviousValue(symbol))
          val prevClockAssigner = makePrevClockAssigner(symbol, prevClockSymbol)
          scheduler.addEndOfCycleAssigner(prevClockAssigner)
        }

      case DefWire(_, name, _) =>
        logger.debug(s"declaration:DefWire:$name")

      case DefRegister(info, name, tpe, clockExpression, resetExpression, initExpression) =>

        logger.debug(s"declaration:DefRegister:$name")

        val registerOut = symbolTable(expand(name))
        val registerIn  = symbolTable(SymbolTable.makeRegisterInputName(registerOut.name))
        val is_sync = !(resetExpression.tpe == AsyncResetType)
        val clock = getDrivingClock(clockExpression)

        if(is_sync) {
          makeAssigner(registerOut, makeGet(registerIn), clock, info = info)
        } else if(clock.isEmpty) {
          makeAssigner(registerOut, makeGet(registerIn), info = info)
        } else {
          makeAsyncRegisterUpdate(registerIn, registerOut, clock.get,
            reset = exprCompiler.processExpression(resetExpression),
            init = exprCompiler.processExpression(initExpression),
            info = info
          )
        }

      case defMemory: DefMemory =>
        val expandedName = expand(defMemory.name)
        logger.debug(s"declaration:DefMemory:${defMemory.name} becomes $expandedName")
        Memory.buildMemoryInternals(defMemory, expandedName, scheduler, compiler = this)

      case _: IsInvalid =>

      case stop @ Stop(info, returnValue, clockExpression, enableExpression) =>
        symbolTable.stopToStopInfo.get(stop) match {
          case Some(stopInfo) =>
            val boolExpression = processStop(stop, exprCompiler.processExpression(enableExpression))

            getDrivingClock(clockExpression) match {
              case Some(clockSymbol) =>
                val prevClockSymbol = symbolTable(SymbolTable.makePreviousValue(clockSymbol))

                val clockTransitionGetter = makeClockTransitionGetter(clockSymbol, prevClockSymbol)
                val stopOp = StopOp(
                  symbol = stopInfo.stopSymbol,
                  info = info,
                  returnValue = returnValue,
                  condition = boolExpression,
                  hasStopped = symbolTable(StopOp.stopHappenedName),
                  dataStore = dataStore,
                  clockTransitionGetter
                )
                addAssigner(stopOp)
              case _ =>
                throw TreadleException(s"Could not find symbol for Stop $stop")
            }

          case _ =>
            throw TreadleException(s"Could not find symbol for Stop $stop")
        }

      case printf @ Print(info, stringLiteral, argExpressions, clockExpression, enableExpression) =>

        symbolTable.printToPrintInfo.get(printf) match {
          case Some(printInfo) =>
            getDrivingClock(clockExpression) match {
              case Some(clockSymbol) =>
                val prevClockSymbol = symbolTable(SymbolTable.makePreviousValue(clockSymbol))

                val clockTransitionGetter = makeClockTransitionGetter(clockSymbol, prevClockSymbol)
                val enable = exprCompiler.processExpression(enableExpression)
                val arguments = argExpressions.map(exprCompiler.processExpression)
                val (boolExpression, args) = processPrintf(printf, enable, arguments)
                val printOp = PrintfOp(printInfo.printSymbol, info, stringLiteral, args, clockTransitionGetter,
                  boolExpression)
                addAssigner(printOp)
              case _ =>
                throw TreadleException(s"Error: no clock found for Print $printf")
            }

          case _ =>
            throw TreadleException(s"Could not find symbol for Print $printf")
        }

      case EmptyStmt =>

      case conditionally: Conditionally =>
        // logger.debug(s"got a conditionally $conditionally")
        throw TreadleException(s"conditionally unsupported in engine $conditionally")
      case _ =>
        println(s"TODO: Unhandled statement $statement")
    }
  }

  def makePrevClockAssigner(clock: Symbol, prevClock: Symbol) : Assigner

  def processTopLevelClocks(module: Module): Unit = {
    module.ports.foreach { port =>
      if(port.tpe == ClockType) {
        val clockSymbol = symbolTable(port.name)
        val prevClockSymbol = symbolTable(SymbolTable.makePreviousValue(clockSymbol))
        val prevClockAssigner = makePrevClockAssigner(clockSymbol, prevClockSymbol)
        scheduler.addEndOfCycleAssigner(prevClockAssigner)
      }
    }
  }

  def processModule(modulePrefix: String, myModule: DefModule, circuit: Circuit): Unit = {
    myModule match {
      case module: firrtl.ir.Module =>
        if(modulePrefix.isEmpty) {
          processTopLevelClocks(module)
        }
        processStatements(modulePrefix, circuit: Circuit, module.body)
      case extModule: ExtModule => // Look to see if we have an implementation for this
        logger.debug(s"got external module ${extModule.name} instance $modulePrefix")
        // all handling of an instance at the compiler stage occurs at a DefInstance above.
    }
  }

  // scalastyle:off cyclomatic.complexity
  def compile(circuit: Circuit, blackBoxFactories: Seq[ScalaBlackBoxFactory]): Unit = {
    val module = FindModule(circuit.main, circuit) match {
      case regularModule: firrtl.ir.Module => regularModule
      case externalModule: firrtl.ir.ExtModule =>
        throw TreadleException(s"Top level module must be a regular module $externalModule")
      case x =>
        throw TreadleException(s"Top level module is not the right kind of module $x")
    }

    processModule("", module, circuit)
  }
}
