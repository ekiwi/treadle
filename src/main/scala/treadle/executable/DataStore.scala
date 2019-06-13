// See LICENSE for license details.

package treadle.executable

import firrtl.ir.Info
import treadle.ScalaBlackBox

import scala.collection.mutable

/**
  * Abstract data store that can be implemented with various underlying representations.
  *
  * @param numberOfBuffers Number of buffers
  */
//scalastyle:off number.of.methods
abstract class DataStore(val numberOfBuffers: Int)
extends DataStoreReader with DataStoreWriter {
  assert(numberOfBuffers >= 0, s"DataStore: numberOfBuffers $numberOfBuffers must be >= 0")
  def makeRollBackBuffer() : RollBackBuffer

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

  case class BlackBoxShim(
      unexpandedName: String,
      outputName:     Symbol,
      inputs:         Seq[Symbol],
      implementation: ScalaBlackBox
  )
  extends BigExpressionResult {

    val dataStore: DataStore = DataStore.this

    def apply(): Big = {
      val inputValues = inputs.map { input => dataStore(input) }
      val bigInt = implementation.getOutput(inputValues, outputName.firrtlType, unexpandedName)
      bigInt
    }
  }

  def apply(symbol: Symbol): Big

  def apply(symbol: Symbol, offset: Int): Big

  def update(symbol: Symbol, value: Big): Unit

  def update(symbol: Symbol, offset: Int, value: Big): Unit

  def makeConstantAssigner(symbol: Symbol, const: Big, info: Info) : Assigner

  def getSymbolFilterFromGetter(expressionResult: ExpressionResult): Option[Symbol => Boolean]

  def makeConstantTriggerAssigner(symbol: Symbol, const: Big, scheduler: Scheduler, triggerOnValue: Int = -1, info: Info) : Assigner

  //scalastyle:off cyclomatic.complexity method.length
  def serialize: String
  def deserialize(jsonString: String): Unit
}

trait DataStoreReader {
  def getValueAtIndex(dataSize: DataSize, index: Int): BigInt
}

trait DataStoreWriter {
  def setValueAtIndex(dataSize: DataSize, index: Int, value: Big): Unit
}

trait DataStoreAllocator {
  def getIndex(dataSize: DataSize, slots: Int = 1): Int
}