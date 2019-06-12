// See LICENSE for license details.

package treadle

import java.io.PrintWriter
import java.util.Calendar

import treadle.chronometry.UTC
import treadle.executable._

/**
  * Works a lot like the chisel classic tester compiles a firrtl input string
  * and allows poke, peek, expect and step
  *
  * pokes invalidate the underlying circuit
  * peek, expect and step, recompute (re-validate) the circuit before executing
  *
  * Important note: port names in LoFirrtl have replaced dot notation with underscore notation
  * so that io.a.b must be referenced as io_a_b
  *
  * @param input              a firrtl program contained in a string
  * @param optionsManager     collection of options for the engine
  */
class TreadleTester(input: String, optionsManager: HasTreadleSuite = new TreadleOptionsManager) {
  var expectationsMet = 0

  treadle.random.setSeed(optionsManager.treadleOptions.randomSeed)

  val wallTime = UTC()

  val engine         : ExecutionEngine  = ExecutionEngine(input, optionsManager, wallTime)
  val treadleOptions : TreadleOptions   = optionsManager.treadleOptions

  wallTime.onTimeChange = () => {
    engine.vcdOption.foreach { vcd =>
      vcd.setTime(wallTime.currentTime)}
  }

  val resetName: String = treadleOptions.resetName
  def setVerbose(value: Boolean = true): Unit = {
    wallTime.isVerbose = value
    engine.setVerbose(value)
  }

  val startTime: Long = System.nanoTime()

  val clockInfoList: Seq[ClockInfo] = if(treadleOptions.clockInfo.isEmpty) {
    if(engine.symbolTable.contains("clock")) {
      Seq(ClockInfo())
    }
    else if(engine.symbolTable.contains("clk")) {
      Seq(ClockInfo("clk"))
    }
    else {
      Seq()
    }
  }
  else {
    treadleOptions.clockInfo
  }

  val clockStepper: ClockStepper = clockInfoList.length match {
    case 0 =>
      new NoClockStepper

    case 1 =>
      val clockInfo = clockInfoList.head
      wallTime.setTime(clockInfo.initialOffset)

      SimpleSingleClockStepper(
        engine,
        engine.dataStore,
        engine.symbolTable(clockInfo.name),
        engine.symbolTable.get(resetName),
        clockInfo.period,
        clockInfo.initialOffset,
        wallTime
      )
    case _ =>
      new MultiClockStepper(engine = this.engine, clockInfoList, wallTime)
  }

  /*
  The Idea here is that combinational delay will be used when a peek follows a poke without a step
  This should allow VCD output to show the events as if they had taken place in a small
  interval of the clock cycle. There is some DANGER here that an unusual test will poke then peek
  over 100 times before calling step, which will create a weird looking clock trace
   */
  val combinationalDelay: Long = {
    clockStepper match {
      case s: SimpleSingleClockStepper =>
        s.clockPeriod / 100
      case m: MultiClockStepper =>
        m.shortestPeriod / 100
      case _ =>
        0
    }
  }

  setVerbose(treadleOptions.setVerbose)

  wallTime.setTime(0L)

  if(engine.verbose) {
    println(s"${"-"*60}\nStarting Treadle at ${Calendar.getInstance.getTime} WallTime: ${wallTime.currentTime}")
  }

  if(treadleOptions.writeVCD) {
    optionsManager.setTopNameIfNotSet(engine.ast.main)
    optionsManager.makeTargetDir()
    engine.makeVCDLogger(
      treadleOptions.vcdOutputFileName(optionsManager),
      treadleOptions.vcdShowUnderscored
    )
  }

  if(optionsManager.treadleOptions.callResetAtStartUp && engine.symbolTable.contains(resetName)) {
    clockInfoList.headOption.foreach { clockInfo =>
      reset(clockInfo.period + clockInfo.initialOffset)
//      reset(clockInfo.period + clockInfo.initialOffset - (clockInfo.period / 2)) // once found this to help on a test
    }
  }

  def reset(timeRaised: Long): Unit = {
    engine.symbolTable.get(resetName).foreach { resetSymbol =>
      engine.setValue(resetName, 1)
      engine.inputsChanged = true

      clockStepper match {
        case _: NoClockStepper =>
          engine.setValue(resetName, 1)
          engine.evaluateCircuit()
          wallTime.incrementTime(timeRaised)
          engine.setValue(resetName, 0)
        case stepper: SimpleSingleClockStepper =>
          clockStepper.addTask(wallTime.currentTime + timeRaised + stepper.downPeriod) { () =>
            engine.setValue(resetName, 0)
            if (engine.verbose) {
              println(s"reset dropped at ${wallTime.currentTime}")
            }
            engine.inputsChanged = true
            engine.evaluateCircuit()
          }
          while(engine.dataStore(resetSymbol) != Big0) {
            stepper.run(1)
          }

        case _ =>
          clockStepper.addTask(wallTime.currentTime + timeRaised) { () =>
            engine.setValue(resetName, 0)
            if (engine.verbose) {
              println(s"reset dropped at ${wallTime.currentTime}")
            }
            engine.inputsChanged = true
          }
          wallTime.runUntil(wallTime.currentTime + timeRaised)
      }
    }
  }

  def makeSnapshot(): Unit = {
    val snapshotName = optionsManager.getBuildFileName(".datastore.snapshot.json")
    val writer = new PrintWriter(snapshotName)
    writer.write(engine.dataStore.serialize)
    writer.close()
    println(s"Writing snapshot file $snapshotName")
  }

  /** Indicate a failure has occurred.  */
  private var failureTime = -1L
  private var failCode: Option[Int] = None
  def fail(code: Int): Unit = {
    if (failCode.isEmpty) {
      failureTime = System.nanoTime()
      failCode = Some(code)
      makeSnapshot()
    }
  }

  /** Indicate failure due to an exception.
    *
    * @param ex exception causing the failure
    * @param msg optional message to be printed
    */
  def fail(ex: Throwable, msg: Option[String ] = None): Nothing = {
    engine.writeVCD()

    msg match {
      case Some(s) => println(s)
      case _ =>
    }
    fail(2)
    throw ex
  }
  def isOK: Boolean = failCode match {
    case None | Some(0) => true
    case _ => false
  }

  /**
    * Pokes value to the port referenced by string
    * Warning: pokes to components other than input ports is currently
    * not supported but does not cause an error warning
    * This feature should be supported soon
    *
    * @param name the name of a port
    * @param value a value to put on that port
    */
  def poke(name: String, value: BigInt): Unit = {
    try {
      val isRegister = engine.symbolTable.isRegister(name)
      engine.setValue(name, value, registerPoke = isRegister)
    }
    catch {
      case ie: TreadleException =>
        fail(ie, Some(s"Error: poke($name, $value)"))
    }
  }

  // TODO: experimental API
  def pokeSymbolic(name: String, symbol: String) : Unit = {
    try {
      val isRegister = engine.symbolTable.isRegister(name)
      engine.setValue(name, value, registerPoke = isRegister)
    }
    catch {
      case ie: TreadleException =>
        fail(ie, Some(s"Error: pokeSymbolic($name, $symbol)"))
    }
  }

  /** inspect a value of a named circuit component
    *
    * @param name the name of a circuit component
    * @return A BigInt value currently set at name
    */
  def peek(name: String): BigInt = {
    if(engine.inputsChanged) {
      if(engine.verbose) {
        println(s"peeking $name on stale circuit, refreshing START")
      }
      engine.evaluateCircuit()
      clockStepper.combinationalBump(combinationalDelay)
      if(engine.verbose) {
        println(s"peeking $name on stale circuit, refreshing DONE")
      }
    }
    engine.getValue(name)
  }

  /**
    * require that a value be present on the named component
 *
    * @param name component name
    * @param expectedValue the BigInt value required
    */
  def expect(name: String, expectedValue: BigInt, message: String = ""): Unit = {
    val value = peek(name)
    if(value != expectedValue) {
      val info = engine.scheduler.getAssignerInfo(name)
      val renderer = new ExpressionViewRenderer(
        engine.dataStore, engine.symbolTable, engine.expressionViews)
      val calculation = renderer.render(engine.symbolTable(name), wallTime.currentTime)
      fail(
        TreadleException(s"Error:expect($name, $expectedValue) got $value $message\n$calculation\nAssigned at: $info")
      )
    }
    expectationsMet += 1
  }

  def cycleCount: Long = clockStepper.cycleCount

  /**
    * Cycles the circuit n steps (with a default of one)
    * At each step registers and memories are advanced and all other elements recomputed
    *
    * @param n cycles to perform
    */
  def step(n: Int = 1): Unit = {
    if(engine.verbose) println(s"In step at ${wallTime.currentTime}")
    clockStepper.run(n)
  }

  /**
    * Pokes value to the named memory at offset
    *
    * @param name  the name of a memory
    * @param index the offset in the memory
    * @param value a value to put on that port
    */
  def pokeMemory(name: String, index: Int, value: BigInt): Unit = {
    engine.symbolTable.get(name) match {
      case Some(_) =>
        engine.setValue(name, value = value, offset = index)
      case _ =>
        throw TreadleException(s"Error: memory $name.forceWrite($index, $value). memory not found")
    }
  }

  def peekMemory(name: String, index: Int): BigInt = {
    engine.symbolTable.get(name) match {
      case Some(_) =>
        engine.getValue(name, offset = index)
      case _ =>
        throw TreadleException(s"Error: get memory $name.forceWrite($index). memory not found")
    }
  }

  /**
    * require that a value be present on the named component
    *
    * @param name component name
    * @param expectedValue the BigInt value required
    */
  def expectMemory(name: String, index: Int, expectedValue: BigInt, message: String = ""): Unit = {
    val value = peekMemory(name, index)
    if(value != expectedValue) {
      val renderer = new ExpressionViewRenderer(
        engine.dataStore, engine.symbolTable, engine.expressionViews)
      val calculation = renderer.render(engine.symbolTable(name), wallTime.currentTime)
      fail(TreadleException (s"Error:expect($name, $expectedValue) got $value $message\n$calculation"))
    }
    expectationsMet += 1
  }


  def reportString: String = {
    val endTime = System.nanoTime()
    val elapsedSeconds = (endTime - startTime).toDouble / 1000000000.0
    /*
        This should not every show the Failed message because currently the engine
        throws an TreadleException on Stop (but maybe that will be made optional at some point)
        Best to leave this here for now, someone might catch the exception manually and still want to
        see this report which should include the Failed in that case
      */
    def status: String = {
      engine.lastStopResult match {
        case Some(stopResult) =>
          s"Failed: Stop result $stopResult:"
        case _ =>
          if (isOK) {
            s"Success:"
          } else {
            s"Failed: Code ${failCode.get}"
          }
      }
    }
    s"test ${engine.ast.main} " +
      s"$status $expectationsMet tests passed " +
      f"in $cycleCount cycles in $elapsedSeconds%.6f seconds ${cycleCount / elapsedSeconds}%.2f Hz"
  }
  /**
    * A simplistic report of the number of expects that passed
    */
  def report(): Unit = {
    engine.writeVCD()
    println(reportString)
  }

  def finish: Boolean = {
    engine.writeVCD()
    isOK
  }
}

object TreadleTester {
  def apply(input : String, optionsManager: HasTreadleSuite = new TreadleOptionsManager): TreadleTester = {
    new TreadleTester(input, optionsManager)
  }
}
