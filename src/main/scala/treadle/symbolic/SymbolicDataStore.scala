// See LICENSE for license details.

package treadle.symbolic

import firrtl.ir.Info
import org.json4s._
import org.json4s.native.JsonMethods._
import org.json4s.JsonDSL._
import treadle.utils.Render
import treadle.executable._
import treadle.symbolic.ValueSummary.SymbolicFun

import scala.collection.mutable


trait SymbolicExpressionResult extends ExpressionResult {
  def apply(): ValueSummary
}


class SymbolicDataStore(numberOfBuffers: Int, dataStoreAllocator: SymbolicDataStoreAllocator)
    (implicit val ctx: SymbolicContext)
    extends DataStore(numberOfBuffers) {
  override def makeRollBackBuffer() : RollBackBuffer = new SymbolicRollBackBuffer(this)

  val numberOfEntries: Int = dataStoreAllocator.numberOfEntries
  val data: Array[Option[ValueSummary]] = Array.fill(numberOfEntries)(None)

  def setValueAtIndex(dataSize: DataSize, index: Int, value: ValueSummary): Unit = {
    data(index) = Some(value)
  }

  def setValueAtIndex(dataSize: DataSize, index: Int, value: Big): Unit = {

    data(index) = Some(ValueSummary() value)
  }

  def getValueAtIndex(dataSize: DataSize, index: Int): Big = data(index).get.concrete

  override def makeConstantAssigner(symbol: Symbol, const: Big, info: Info) : Assigner = {
    val cc = symbol.valueFrom(const)
    Assign(symbol, () => ValueSummary(cc, symbol.bitWidth), info)
  }

  override def getSymbolFilterFromGetter(expressionResult: ExpressionResult): Option[Symbol => Boolean] = {
    expressionResult match {
      case Get(index) => Some({sym : Symbol => sym.index == index})
      case _ => None
    }
  }

  case class Get(index: Int) extends SymbolicExpressionResult {
    def apply(): ValueSummary = data(index).get
  }

  case class Assign(symbol: Symbol, expression: () => ValueSummary, info: Info) extends Assigner {
    val index: Int = symbol.index

    def runLean(): Unit = {
      data(index) = Some(expression())
    }

    def runFull(): Unit = {
      runLean()
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


  def apply(symbol: Symbol): Big = {
    symbol.dataSize match {
      case IntSize  => intData(symbol.index)
      case LongSize => longData(symbol.index)
      case BigSize  => bigData(symbol.index)
    }
  }

  def apply(symbol: Symbol, offset: Int): Big = {
    symbol.dataSize match {
      case IntSize  => intData(symbol.index + offset)
      case LongSize => longData(symbol.index + offset)
      case BigSize  => bigData(symbol.index + offset)
    }
  }

  def update(symbol: Symbol, value: Big): Unit = {
    symbol.dataSize match {
      case IntSize  => intData(symbol.index) = value.toInt
      case LongSize => longData(symbol.index) = value.toLong
      case BigSize  => bigData(symbol.index) = value
    }
  }

  def update(symbol: Symbol, offset: Int, value: Big): Unit = {
    if(offset >= symbol.slots) {
      throw TreadleException(s"assigning to memory ${symbol.name}[$offset] <= $value: index out of range")
    }
    symbol.dataSize match {
      case IntSize  => intData(symbol.index + offset) = value.toInt
      case LongSize => longData(symbol.index + offset) = value.toLong
      case BigSize  => bigData(symbol.index + offset) = value
    }
  }

  override def makeConstantTriggerAssigner(symbol: Symbol, const: Big, scheduler: Scheduler,
                                           triggerOnValue: Int = -1, info: Info) : Assigner = {
    val cc = symbol.valueFrom(const)
    symbol.dataSize match {
      case IntSize  => TriggerIntAssigner(symbol, scheduler, GetIntConstant(cc.toInt).apply, triggerOnValue, info)
      case LongSize => throw new RuntimeException("long constants not supported!")
      case BigSize  => throw new RuntimeException("big constants not supported!")
    }
  }


  case class TriggerIntAssigner(
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


  //scalastyle:off cyclomatic.complexity method.length
  def serialize: String = { throw new NotImplementedError("Serializing symbolic executions is not supported!") }

  def deserialize(jsonString: String): Unit = {
    throw new NotImplementedError("Serializing symbolic executions is not supported!")
  }

}

class SymbolicDataStoreAllocator extends DataStoreAllocator {
  private var nextIndex : Int = 0

  def numberOfEntries : Int = nextIndex

  def getIndex(dataSize: DataSize, slots: Int = 1): Int = {
    val index = nextIndex
    nextIndex += slots
    index
  }
}

class SymbolicRollBackBuffer(dataStore: SymbolicDataStore) extends RollBackBuffer {
  var time: Long = 0L

  val data : Array[Option[ValueSummary]]  = Array.fill(dataStore.numberOfEntries)(None)

  def getValueAtIndex(dataSize: DataSize, index: Int): Big = data(index).get.concrete

  def dump(dumpTime: Long): Unit = {
    time = dumpTime
    Array.copy(dataStore.data,  0, data,  0, data.length)
  }
}

object SymbolicDataStore {
  def apply(numberOfBuffers: Int, dataStoreAllocator: FastDataStoreAllocator): FastDataStore = {
    new FastDataStore(numberOfBuffers, dataStoreAllocator)
  }
  def allocator(): FastDataStoreAllocator = new FastDataStoreAllocator
}