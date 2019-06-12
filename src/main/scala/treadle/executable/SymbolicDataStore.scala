// See LICENSE for license details.

package treadle.executable

import firrtl.ir.Info
import org.json4s._
import org.json4s.native.JsonMethods._
import org.json4s.JsonDSL._
import treadle.ScalaBlackBox
import treadle.utils.Render

import scala.collection.mutable


class SymbolicDataStore(numberOfBuffers: Int, dataStoreAllocator: SymbolicDataStoreAllocator)
extends BasicDataStore(numberOfBuffers) {
  def numberOfEntries : Int = dataStoreAllocator.getSize
  val data: Array[BigInt] = Array.fill(numberOfEntries)(BigInt(0))
}

//scalastyle:off number.of.methods
abstract class BasicDataStore(val numberOfBuffers: Int) {
  assert(numberOfBuffers >= 0, s"DataStore: numberOfBuffers $numberOfBuffers must be >= 0")

  var leanMode      : Boolean = true
  val plugins       : mutable.HashMap[String, DataStorePlugin] = new mutable.HashMap()
  val activePlugins : mutable.ArrayBuffer[DataStorePlugin]     = new mutable.ArrayBuffer()

  def addPlugin(name: String, plugin: DataStorePlugin, enable: Boolean): Unit = {
    if(plugins.contains(name)) {
      throw TreadleException(s"Attempt to add already loaded plugin $name new $plugin, existing ${plugins(name)}")
    }
    plugins(name) = plugin
    plugin.setEnabled(enable)
  }

  def enablePlugin(name: String): Unit = {
    if(plugins.contains(name)) {
      println(s"Could not find plugin $name to remove it")
    }
    plugins(name).setEnabled(true)
  }

  def disablePlugin(name: String): Unit = {
    if(plugins.contains(name)) {
      println(s"Could not find plugin $name to remove it")
    }
    plugins(name).setEnabled(false)
  }

  def removePlugin(name: String): Unit = {
    if(plugins.contains(name)) {
      println(s"Could not find plugin $name to remove it")
    }
    val plugin = plugins(name)
    plugin.setEnabled(false)  // remove from active and should return to lean mode if no other plugins are active
    plugins.remove(name)
  }

  def hasEnabledPlugins: Boolean = {
    activePlugins.nonEmpty
  }

  var executionEngineOption: Option[ExecutionEngine] = None

  def setExecutionEngine(executionEngine: ExecutionEngine): Unit = {
    executionEngineOption = Some(executionEngine)

    executionEngine.optionsManager.treadleOptions.symbolsToWatch.foreach { symbolName =>
      if (executionEngine.symbolTable.contains(symbolName)) {
        watchList += executionEngine.symbolTable(symbolName)
      }
      else {
        throw TreadleException(s"treadleOptions.symbols to watch has bad symbolName $symbolName")
      }
    }

    setAssignmentDisplayModes()
  }

  def setAssignmentDisplayModes(): Unit = {
    executionEngineOption.foreach { executionEngine =>
      val watchList = executionEngine.optionsManager.treadleOptions.symbolsToWatch.map { symbolName =>
        executionEngine.symbolTable.get(symbolName) match {
          case Some(symbol) =>
            symbol
          case _ =>
            throw TreadleException(s"treadleOptions.symbols to watch has bad symbolName $symbolName")
        }
      }

      val verbose = executionEngineOption.get.verbose
      executionEngine.scheduler.combinationalAssigns.foreach { assigner =>
        val render = watchList.contains(assigner.symbol)
        assigner.setLeanMode(!verbose && !render)
        assigner.setVerbose(verbose)
        assigner.setRender(render)
      }
    }
  }

  val watchList: mutable.HashSet[Symbol] = new mutable.HashSet()

  val rollBackBufferManager = new RollBackBufferManager(this)
  def saveData(clockName: String, time: Long): Unit = {
    if(numberOfBuffers > 0) {
      rollBackBufferManager.saveData(clockName, time)
    }
  }

  def runPlugins(symbol: Symbol, offset: Int = -1): Unit = {
    activePlugins.foreach { _.run(symbol, offset) }
  }

  def showAssignment(symbol: Symbol): Unit = {
    val showValue = symbol.normalize(apply(symbol))
    println(s"${symbol.name} <= $showValue h${showValue.toString(16)}")
  }

  def showIndirectAssignment(symbol: Symbol, value: BigInt, index: Int): Unit = {
    //TODO (chick) Need to build in display of index computation
    val showValue = symbol.normalize(value)
    println(s"${symbol.name}($index) <= $showValue")
  }

  def renderAssignment(symbol: Symbol): Unit = {
    executionEngineOption.foreach { executionEngine =>
      println(executionEngine.renderComputation(symbol.name))
    }
  }

  def getRegisterLastValueIndex(symbol: Symbol): Int = {
    executionEngineOption match {
      case Some(executionEngine) =>
        executionEngine.symbolTable(SymbolTable.makeLastValueName(symbol)).index
      case _ =>
        throw TreadleException(s"Could not find clock last value index for $symbol")
    }
  }

  case class GetInt(index: Int) extends IntExpressionResult {
    def apply(): Int = intData(index)
  }

  case class AssignInt(symbol: Symbol, expression: FuncInt, info: Info) extends Assigner {
    val index: Int = symbol.index

    def runLean(): Unit = {
      intData(index) = expression()
    }

    def runFull(): Unit = {
      val value = expression()
      intData(index) = value
      runPlugins(symbol)
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean else runFull
    }
    var run: FuncUnit = runLean
  }

  case class TriggerConstantAssigner(
    symbol: Symbol,
    scheduler: Scheduler,
    triggerOnValue: Int = -1,
    info: Info
  ) extends Assigner {

    val index: Int = symbol.index

    var value: Int = 0
    var lastValue: Int = 0

    def runLean(): Unit = {
      lastValue = intData(index)
      intData(index) = value
      if(value == triggerOnValue && lastValue != triggerOnValue) {
        scheduler.executeTriggeredAssigns(symbol)
      }
      else if(value != triggerOnValue && lastValue == triggerOnValue) {
        scheduler.executeTriggeredUnassigns(symbol)
      }
    }

    def runFull(): Unit = {
      lastValue = intData(index)
      intData(index) = value

      runPlugins(symbol)

      if(value == triggerOnValue && lastValue != triggerOnValue) {
        if(isVerbose) Render.headerBar(s"triggered assigns for ${symbol.name}", offset = 8)
        scheduler.executeTriggeredAssigns(symbol)
        if(isVerbose) Render.headerBar(s"done triggered assigns for ${symbol.name}", offset = 8)
      }
      else if(value != triggerOnValue && lastValue == triggerOnValue) {
        if(scheduler.triggeredUnassigns.contains(symbol)) {
          if(isVerbose) Render.headerBar(s"triggered un-assigns for ${symbol.name}", offset = 8)
          scheduler.executeTriggeredUnassigns(symbol)
          if(isVerbose) Render.headerBar(s"done triggered un-assigns for ${symbol.name}", offset = 8)
        }
      }
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean else runFull
    }
    var run: FuncUnit = runLean
  }

  case class TriggerExpressionAssigner(
    symbol: Symbol,
    scheduler: Scheduler,
    expression: FuncInt,
    triggerOnValue: Int = -1,
    info: Info
  ) extends Assigner {

    val index: Int = symbol.index

    var lastValue: Int = 0

    def runLean(): Unit = {
      lastValue = intData(index)
      val value = expression()
      intData(index) = value
      if(value == triggerOnValue && lastValue != triggerOnValue) {
        scheduler.executeTriggeredAssigns(symbol)
      }
      else if(value != triggerOnValue && lastValue == triggerOnValue) {
        scheduler.executeTriggeredUnassigns(symbol)
      }
    }

    def runFull(): Unit = {
      lastValue = intData(index)
      val value = expression()
      intData(index) = value

      runPlugins(symbol)

      if(value == triggerOnValue && lastValue != triggerOnValue) {
        if(isVerbose) Render.headerBar(s"triggered assigns for ${symbol.name}", offset = 8)
        scheduler.executeTriggeredAssigns(symbol)
        if(isVerbose) Render.headerBar(s"done triggered assigns for ${symbol.name}", offset = 8)
      }
      else if(value != triggerOnValue && lastValue == triggerOnValue) {
        if(scheduler.triggeredUnassigns.contains(symbol)) {
          if(isVerbose) Render.headerBar(s"triggered un-assigns for ${symbol.name}", offset = 8)
          scheduler.executeTriggeredUnassigns(symbol)
          if(isVerbose) Render.headerBar(s"done triggered un-assigns for ${symbol.name}", offset = 8)
        }
      }
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean else runFull
    }
    var run: FuncUnit = runLean
  }

  case class GetLong(index: Int) extends LongExpressionResult {
    def apply(): Long = longData(index)
  }

  case class AssignLong(symbol: Symbol, expression: FuncLong, info: Info) extends Assigner {
    val index: Int = symbol.index

    def runLean(): Unit = {
      longData(index) = expression()
    }

    def runFull(): Unit = {
      val value = expression()
      longData(index) = value
      runPlugins(symbol)
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) {
        runLean
      } else {
        runFull
      }
    }
    var run: FuncUnit = runLean
  }

  case class GetBig(index: Int) extends BigExpressionResult {
    def apply(): Big = bigData(index)
  }

  case class AssignBig(symbol: Symbol, expression: FuncBig, info: Info) extends Assigner {
    val index: Int = symbol.index

    def runLean(): Unit = {
      bigData(index) = expression()
    }
    def runFull(): Unit = {
      val value = expression()
      bigData(index) = value
      runPlugins(symbol)
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean else runFull
    }
    var run: FuncUnit = runLean
  }

  /** for memory implementations */
  case class GetIntIndirect(
                             memorySymbol: Symbol,
                             getMemoryIndex: FuncInt,
                             enable: FuncInt
                           ) extends IntExpressionResult {
    val memoryLocation: Int = memorySymbol.index
    def apply(): Int = {
      intData(memoryLocation + (getMemoryIndex() % memorySymbol.slots))
    }
  }

  case class GetLongIndirect(
    memorySymbol: Symbol,
    getMemoryIndex: FuncInt,
    enable: FuncInt
  ) extends LongExpressionResult {
    val memoryLocation: Int = memorySymbol.index
    def apply(): Long = {
      longData(memoryLocation + (getMemoryIndex() % memorySymbol.slots))
    }
  }

  case class GetBigIndirect(
    memorySymbol: Symbol,
    getMemoryIndex: FuncInt,
    enable: FuncInt
  ) extends BigExpressionResult {
    val memoryLocation: Int = memorySymbol.index
    def apply(): Big = {
      bigData(memoryLocation + (getMemoryIndex() % memorySymbol.slots))
    }
  }

  case class AssignIntIndirect(
    symbol: Symbol,
    memorySymbol: Symbol,
    getMemoryIndex: FuncInt,
    enable: FuncInt,
    expression: FuncInt,
    info: Info
  ) extends Assigner {
    val index: Int = memorySymbol.index

    def runLean(): Unit = {
      if(enable() > 0) {
        intData(index + getMemoryIndex.apply()) = expression()
      }
    }

    def runFull(): Unit = {
      if(enable() > 0) {
        val value = expression()
        val memoryIndex = getMemoryIndex.apply()
        intData(index + (memoryIndex % memorySymbol.slots)) = value
        runPlugins(memorySymbol, memoryIndex)
      }
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean else runFull
    }
    var run: FuncUnit = runLean
  }

  case class AssignLongIndirect(
    symbol: Symbol,
    memorySymbol: Symbol,
    getMemoryIndex: FuncInt,
    enable: FuncInt,
    expression: FuncLong,
    info: Info
  ) extends Assigner {
    val index: Int = memorySymbol.index

    def runLean(): Unit = {
      if(enable() > 0) {
        longData(index + (getMemoryIndex.apply() % memorySymbol.slots)) = expression()
      }
    }

    def runFull(): Unit = {
      if(enable() > 0) {
        val value = expression()
        val memoryIndex = getMemoryIndex.apply()
        longData(index + (memoryIndex % memorySymbol.slots)) = value
        runPlugins(memorySymbol, memoryIndex)
      }
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean else runFull
    }
    var run: FuncUnit = runLean
  }

  case class AssignBigIndirect(
    symbol: Symbol,
    memorySymbol: Symbol,
    getMemoryIndex: FuncInt,
    enable: FuncInt,
    expression: FuncBig,
    info: Info
  ) extends Assigner {
    val index: Int = memorySymbol.index

    def runLean(): Unit = {
      if(enable() > 0) {
        bigData(index + (getMemoryIndex.apply() % memorySymbol.slots)) = expression()
      }
    }

    def runFull(): Unit = {
      if(enable() > 0) {
        val value = expression()
        val memoryIndex = getMemoryIndex.apply()
        bigData(index + (memoryIndex % memorySymbol.slots)) = value
        runPlugins(memorySymbol, memoryIndex)
      }
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean else runFull
    }
    var run: FuncUnit = runLean
  }

}

object SymbolicDataStore {
  def apply(numberOfBuffers: Int, dataStoreAllocator: SymbolicDataStoreAllocator): DataStore = {
    new DataStore(numberOfBuffers, dataStoreAllocator)
  }
  def allocator(): DataStoreAllocator = new SymbolicDataStoreAllocator
}

class SymbolicDataStoreAllocator extends DataStoreAllocator {
  private var index = 0

  def getSize: Int = index

  def getIndex(dataSize: DataSize, slots: Int = 1): Int = {
    val ii = index
    index += slots
    ii
  }
}
