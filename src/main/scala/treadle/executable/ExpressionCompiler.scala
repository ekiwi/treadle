// See LICENSE for license details.

package treadle.executable

import firrtl.PrimOps._
import firrtl._
import firrtl.ir._
import treadle._
import treadle.utils.FindModule

abstract class ExpressionCompiler(
    val symbolTable  : SymbolTable,
    val dataStore    : DataStore,
    scheduler        : Scheduler,
    treadleOptions   : TreadleOptions,
    blackBoxFactories: Seq[ScalaBlackBoxFactory]
)
  extends logger.LazyLogging {

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

  def makeGet(source: Symbol): ExpressionResult

  def makeGet(sourceName: String): ExpressionResult = {
    makeGet(symbolTable(sourceName))
  }

  def makeGetIndirect(memory: Symbol, data: Symbol, enable: Symbol, addr: Symbol): ExpressionResult

  def makeAnd(e1: ExpressionResult, e2: ExpressionResult, resultWidth: Int): ExpressionResult

  //scalastyle:off cyclomatic.complexity
  def makeAssigner(symbol: Symbol, expressionResult: ExpressionResult,
                   triggerOption: Option[Symbol] = None, info: Info): Unit
  def createAssigner(symbol: Symbol, expressionResult: ExpressionResult, info: Info): Assigner


  def addAssigner(assigner: Assigner, triggerOption: Option[Symbol] = None): Unit = {
    val symbol = assigner.symbol
    scheduler.addAssigner(symbol, assigner, triggerOption)
  }

  def makeIndirectAssigner(
    portSymbol       : Symbol,
    memorySymbol     : Symbol,
    memoryIndex      : Int,
    enableIndex      : Int,
    expressionResult : ExpressionResult,
    clock            : Symbol,
    info             : Info
  ): Unit

  def binaryOps(modulePrefix: String, opCode: PrimOp, args: Seq[Expression], tpe: Type): ExpressionResult
  def oneArgOneParamOps(modulePrefix: String, op: PrimOp, expressions: Seq[Expression],
                        ints: Seq[BigInt], tpe: firrtl.ir.Type): ExpressionResult
  def oneArgTwoParamOps(modulePrefix: String, op: PrimOp, expressions: Seq[Expression],
                        ints: Seq[BigInt], tpe: firrtl.ir.Type): ExpressionResult
  def unaryOps(modulePrefix: String, op: PrimOp, expressions: Seq[Expression], tpe: firrtl.ir.Type): ExpressionResult
  def processMux(condition: ExpressionResult, trueExpression: ExpressionResult,
                 falseExpression: ExpressionResult): ExpressionResult

  /*
  * Process loFirrtl expression and return an executable result
  *
  * @param expression a loFirrtlExpression
  * @return
  */
  //scalastyle:off method.length
  def processExpression(modulePrefix: String, expression: Expression): ExpressionResult = {
    def expand(name: String): String = if(modulePrefix.isEmpty) name else modulePrefix + "." + name
    val result: ExpressionResult = expression match {
      case Mux(condition, trueExpression, falseExpression, _) =>
        processMux(
          processExpression(modulePrefix, condition),
          processExpression(modulePrefix, trueExpression),
          processExpression(modulePrefix, falseExpression)
        )
      case WRef(name, _, _, _) =>
        makeGet(expand(name))
      case subfield: WSubField =>
        makeGet(expand(subfield.serialize))
      case subIndex: WSubIndex =>
        makeGet(expand(subIndex.serialize))

      case ValidIf(condition, value, tpe) =>
        if(treadleOptions.validIfIsRandom) {
          processExpression(modulePrefix, condition) match {
            case c: IntExpressionResult =>
              processExpression(modulePrefix, value) match {
                case t: IntExpressionResult =>
                  MuxInts(c.apply, t.apply, UndefinedInts(getWidth(tpe)).apply)
                case t: LongExpressionResult =>
                  MuxLongs(c.apply, t.apply, UndefinedLongs(getWidth(tpe)).apply)
                case t: BigExpressionResult =>
                  MuxBigs(c.apply, t.apply, UndefinedBigs(getWidth(tpe)).apply)
                case _ =>
                  throw TreadleException(s"Mux condition is not 1 bit $condition parsed as $c")
              }
            case c =>
              throw TreadleException(s"Mux condition is not 1 bit $condition parsed as $c")
          }
        }
        else {
          processExpression(modulePrefix, value)
        }
      case DoPrim(op, args, const, tpe) =>
        val v = op match {
          case Add => binaryOps(modulePrefix, op, args, tpe)
          case Sub => binaryOps(modulePrefix, op, args, tpe)
          case Mul => binaryOps(modulePrefix, op, args, tpe)
          case Div => binaryOps(modulePrefix, op, args, tpe)
          case Rem => binaryOps(modulePrefix, op, args, tpe)

          case Eq  => binaryOps(modulePrefix, op, args, tpe)
          case Neq => binaryOps(modulePrefix, op, args, tpe)
          case Lt  => binaryOps(modulePrefix, op, args, tpe)
          case Leq => binaryOps(modulePrefix, op, args, tpe)
          case Gt  => binaryOps(modulePrefix, op, args, tpe)
          case Geq => binaryOps(modulePrefix, op, args, tpe)

          case Pad     => unaryOps(modulePrefix, op, args, tpe)

          case AsUInt  => unaryOps(modulePrefix, op, args, tpe)
          case AsSInt  => unaryOps(modulePrefix, op, args, tpe)
          case AsClock => unaryOps(modulePrefix, op, args, tpe)

          case Shl => oneArgOneParamOps(modulePrefix, op, args, const, tpe)
          case Shr => oneArgOneParamOps(modulePrefix, op, args, const, tpe)

          case Dshl => binaryOps(modulePrefix, op, args, tpe)
          case Dshr => binaryOps(modulePrefix, op, args, tpe)

          case Cvt => unaryOps(modulePrefix, op, args, tpe)
          case Neg => unaryOps(modulePrefix, op, args, tpe)
          case Not => unaryOps(modulePrefix, op, args, tpe)

          case And => binaryOps(modulePrefix, op, args, tpe)
          case Or  => binaryOps(modulePrefix, op, args, tpe)
          case Xor => binaryOps(modulePrefix, op, args, tpe)

          case Andr => unaryOps(modulePrefix, op, args, tpe)
          case Orr =>  unaryOps(modulePrefix, op, args, tpe)
          case Xorr => unaryOps(modulePrefix, op, args, tpe)

          case Cat => binaryOps(modulePrefix, op, args, tpe)

          case Bits => oneArgTwoParamOps(modulePrefix, op, args, const, tpe)

          case Head => oneArgOneParamOps(modulePrefix, op, args, const, tpe)
          case Tail => oneArgOneParamOps(modulePrefix, op, args, const, tpe)
          case _ =>
            throw new Exception(s"processExpression:error: unhandled expression $expression")
        }
        v
      case UIntLiteral(value, IntWidth(width)) =>
        DataSize(width) match {
          case IntSize  => GetIntConstant(value.toInt)
          case LongSize => GetLongConstant(value.toLong)
          case BigSize  => GetBigConstant(value)
        }
      case SIntLiteral(value, IntWidth(width)) =>
        DataSize(width) match {
          case IntSize  => GetIntConstant(value.toInt)
          case LongSize => GetLongConstant(value.toLong)
          case BigSize  => GetBigConstant(value)
        }
      case _ =>
        throw TreadleException(s"bad expression $expression")
    }
    result
  }

  //scalastyle:off method.length
  def processStatements(modulePrefix: String, circuit: Circuit, statement: firrtl.ir.Statement): Unit = {
    val expand = (name: String) => if(modulePrefix.isEmpty) name else modulePrefix + "." + name

    def getDrivingClock(clockExpression: Expression): Option[Symbol] = {

      clockExpression match {
        case WRef(clockName, _, _, _) =>
          for {
            clockSym <- symbolTable.get(expand(clockName))
            topClock <- symbolTable.findHighestClock(clockSym)
          } yield {
            topClock
          }
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

          val processedExpression = processExpression(modulePrefix, con.expr)

          makeAssigner(registerIn, processedExpression, info = con.info)
        }
        else {
          val assignedSymbol = symbolTable(expandedName)
          makeAssigner(assignedSymbol, processExpression(modulePrefix, con.expr), info = con.info)

          if(assignedSymbol.firrtlType == ClockType) {
            getDrivingClock(con.expr).foreach { drivingClock =>
              val clockDown = symbolTable(drivingClock.name)
              val downAssigner = createAssigner(assignedSymbol, makeGet(drivingClock), con.info)
              scheduler.addUnassigner(drivingClock, downAssigner)
            }
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
                    val shim = dataStore.BlackBoxShim(port.name, portSymbol, inputSymbols, implementation)
                    makeAssigner(portSymbol, shim, info = info)
                  }
                  if (port.tpe == ClockType) {
                    val clockSymbol = symbolTable(expand(instanceName + "." + port.name))
                    val blackBoxCycler = BlackBoxCycler(instanceSymbol, implementation, clockSymbol, dataStore, info)

                    val drivingClockOption = symbolTable.findHighestClock(clockSymbol)

                    scheduler.addAssigner(instanceSymbol, blackBoxCycler, triggerOption = drivingClockOption)
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
        makeAssigner(symbol, processExpression(modulePrefix, expression), info = info)

      case DefWire(_, name, _) =>
        logger.debug(s"declaration:DefWire:$name")

      case DefRegister(info, name, _, clockExpression, _, _) =>

        logger.debug(s"declaration:DefRegister:$name")

        val registerOut = symbolTable(expand(name))
        val registerIn  = symbolTable(SymbolTable.makeRegisterInputName(registerOut.name))

        val drivingClockOption = getDrivingClock(clockExpression)

        makeAssigner(registerOut, makeGet(registerIn), drivingClockOption, info = info)

      case defMemory: DefMemory =>
        val expandedName = expand(defMemory.name)
        logger.debug(s"declaration:DefMemory:${defMemory.name} becomes $expandedName")
        Memory.buildMemoryInternals(defMemory, expandedName, scheduler, compiler = this)

      case _: IsInvalid =>

      case stop @ Stop(info, returnValue, clockExpression, enableExpression) =>
        symbolTable.stopToStopInfo.get(stop) match {
          case Some(stopInfo) =>
            val intExpression = processExpression(modulePrefix, enableExpression) match {
              case i : IntExpressionResult  => i
              case l : LongExpressionResult => LongToInt(l.apply)
              case b : BigExpressionResult  => ToInt(b.apply)
              case _ =>
                throw TreadleException(s"Error: stop $stop has unknown condition type")
            }

            val stopOp = StopOp(
              symbol          = stopInfo.stopSymbol,
              info            = info,
              returnValue     = returnValue,
              condition       = intExpression,
              hasStopped      = symbolTable(StopOp.stopHappenedName),
              dataStore       = dataStore
            )
            val drivingClockOption = getDrivingClock(clockExpression)
            addAssigner(stopOp, triggerOption = drivingClockOption)

          case _ =>
            throw TreadleException(s"Could not find symbol for Stop $stop")
        }

      case printf @ Print(info, stringLiteral, argExpressions, clockExpression, enableExpression) =>

        symbolTable.printToPrintInfo.get(printf) match {
          case Some(printInfo) =>
            val intExpression = processExpression(modulePrefix, enableExpression) match {
              case i : IntExpressionResult  => i
              case l : LongExpressionResult => LongToInt(l.apply)
              case b : BigExpressionResult  => ToInt(b.apply)
              case _ =>
                throw TreadleException(s"Error: printf $printf has unknown condition type")
            }

            val printOp = PrintfOp(
              printInfo.printSymbol,
              info, stringLiteral,
              argExpressions.map { expression => processExpression(modulePrefix, expression) },
              intExpression,
              dataStore
            )
            val drivingClockOption = getDrivingClock(clockExpression)
            addAssigner(printOp, triggerOption = drivingClockOption)

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
  // scalastyle:on

  def processModule(modulePrefix: String, myModule: DefModule, circuit: Circuit): Unit = {
    def expand(name: String): String = if(modulePrefix.isEmpty) name else modulePrefix + "." + name

    myModule match {
      case module: firrtl.ir.Module =>
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

    scheduler.registerClocks ++= FindRegisterClocks.run(module, circuit, symbolTable)

    processModule("", module, circuit)

    scheduler.sortInputSensitiveAssigns()
  }
}
