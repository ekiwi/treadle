// See LICENSE for license details.

package treadle.executable

import firrtl.ir.Info
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

trait DataPluginHost {
  def addPlugin(name: String, plugin: DataStorePlugin, enable: Boolean): Unit
  def removePlugin(name: String): Unit
  def hasEnabledPlugins: Boolean
  val plugins : mutable.HashMap[String, DataStorePlugin]   // TODO: change to getter
  val activePlugins : mutable.ArrayBuffer[DataStorePlugin] // TODO: change to getter

}

/** A DataBuffer is the a snapshot of a [[AbstractDataStore]] at a particular time. */
trait DataBuffer extends DataReader {
  def getTime: Long
  def dump(dumpTime: Long): Unit
}

trait AbstractDataStore extends DataReader with DataWriter with DataSerializer with DataPluginHost {
  var leanMode : Boolean
  val numberOfBuffers: Int
  def setExecutionEngine(executionEngine: ExecutionEngine): Unit
  def saveData(time: Long): Unit
  def findBufferBeforeClockTransition(time: Long, clock: Symbol, prevClock: Symbol): Option[DataBuffer]
  def makeConstantAssigner(symbol: Symbol, value: Big, info: Info) : Assigner
  def getWaveformValues(symbols: Array[Symbol], startCycle: Int = 0, endCycle: Int = -1): WaveformValues
}
