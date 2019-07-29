// See LICENSE for license details.

package treadle.executable

import firrtl.ir.Info
import org.json4s._
import org.json4s.native.JsonMethods._
import org.json4s.JsonDSL._
import treadle.ScalaBlackBox

import scala.collection.mutable

trait DataReader {
  def apply(symbol: Symbol): Big
  def apply(symbol: Symbol, offset: Int): Big
}

trait DataWriter {
  def update(symbol: Symbol, value: Big): Unit
  def update(symbol: Symbol, offset: Int, value: Big): Unit
}

trait DataSerializer {
  def serialize: String
  def deserialize(jsonString: String): Unit
}

trait DataPluginManager {
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

  def runPlugins(symbol: Symbol, offset: Int = -1): Unit = {
    activePlugins.foreach { _.run(symbol, offset) }
  }
}

trait ExecutionEngineLoader {
  protected val watchList: mutable.HashSet[Symbol] = new mutable.HashSet()
  protected var executionEngineOption: Option[ExecutionEngine] = None

  def setExecutionEngine(executionEngine: ExecutionEngine): Unit = {
    executionEngineOption = Some(executionEngine)

    executionEngine.symbolsToWatch.foreach { symbolName =>
      if (executionEngine.symbolTable.contains(symbolName)) {
        watchList += executionEngine.symbolTable(symbolName)
      }
      else {
        throw TreadleException(s"treadleOptions.symbols to watch has bad symbolName $symbolName")
      }
    }

    setAssignmentDisplayModes()
  }

  private def setAssignmentDisplayModes(): Unit = {
    executionEngineOption.foreach { executionEngine =>
      val watchList = executionEngine.symbolsToWatch.map { symbolName =>
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
}

/** A DataBuffer is the a snapshot of a [[AbstractDataStore]] at a particular time. */
trait DataBuffer extends DataReader {
  def getTime: Long
  def dump(dumpTime: Long): Unit
}

trait AbstractDataStore extends DataReader with DataWriter with DataSerializer with DataPluginManager
    with ExecutionEngineLoader {
  var leanMode : Boolean
  val numberOfBuffers: Int
  def saveData(time: Long): Unit
  def findBufferBeforeClockTransition(time: Long, clock: Symbol, prevClock: Symbol): Option[DataBuffer]
  def makeConstantAssigner(symbol: Symbol, value: Big, info: Info) : Assigner
  def getWaveformValues(symbols: Array[Symbol], startCycle: Int = 0, endCycle: Int = -1): WaveformValues
}
