// See LICENSE for license details.

package treadle.executable.simple

import treadle.executable._
import firrtl.ir.Info
import org.json4s._
import org.json4s.native.JsonMethods._
import org.json4s.JsonDSL._


class DataStore(allocator: DataStoreAllocator) extends AbstractDataStore {
  val numberOfBuffers: Int = 0

  val data: Array[Big] = Array.fill(allocator.getSize)(Big(0))
  def apply(symbol: Symbol): Big = data(symbol.index)
  def apply(symbol:Symbol, offset: Int): Big = {
    assert(offset < symbol.slots)
    data(symbol.index + offset)
  }

  def update(symbol: Symbol, value: Big): Unit = { data(symbol.index) = value }
  def update(symbol: Symbol, offset: Int, value: Big): Unit = {
    if (offset >= symbol.slots) {
      throw TreadleException(s"assigning to memory ${symbol.name}[$offset] <= $value: index out of range")
    }
    data(symbol.index + offset) = value
  }

  // we do not provide any rollback buffer support
  def findBufferBeforeClockTransition(time: Long, clock: Symbol, prevClock: Symbol): Option[DataBuffer] = None
  def saveData(time: Long): Unit = {}


  def makeConstantAssigner(symbol: Symbol, value: Big, info: Info) : Assigner = {
    Assign(symbol, GetBigConstant(value).apply _, info)
  }

  case class Get(index: Int) extends BigExpressionResult {
    def apply(): Big = data(index)
  }

  case class Assign(symbol: Symbol, expression: FuncBig, info: Info) extends Assigner {
    val run = ()=> {
      val value = if( symbol.forcedValue.isDefined) { symbol.forcedValue.get } else { expression() }
      data(symbol.index) = value
      runPlugins(symbol)
    }
    // we ignore the lean mode setting for simplicity's sake
    override def setLeanMode(isLean: Boolean): Unit = {}
  }

  case class GetIndirect(memorySymbol: Symbol, getMemoryIndex: FuncBig, enable: FuncBig) extends BigExpressionResult {
    val memoryLocation: Int = memorySymbol.index
    def apply(): Big = {
      data(memoryLocation + (getMemoryIndex().toInt % memorySymbol.slots))
    }
  }

  case class AssignIndirect(
    symbol: Symbol,
    memorySymbol: Symbol,
    getMemoryIndex: FuncBig,
    enable: FuncBig,
    expression: FuncBig,
    info: Info
  ) extends Assigner {
    val run = ()=> {
      if(enable() > 0) {
        val value = if( symbol.forcedValue.isDefined) { symbol.forcedValue.get } else { expression() }
        val memoryIndex = getMemoryIndex.apply().toInt
        val offset = memoryIndex % memorySymbol.slots
        data(memorySymbol.index + offset) = value
        runPlugins(memorySymbol, memoryIndex.toInt)
      }
    }
    // we ignore the lean mode setting for simplicity's sake
    override def setLeanMode(isLean: Boolean): Unit = {}
  }

  def getWaveformValues(symbols: Array[Symbol], startCycle: Int = 0, endCycle: Int = -1): WaveformValues = {
    val clockValues = new Array[BigInt](0)
    val symbolValues = Array.ofDim[BigInt](symbols.length, 0)
    WaveformValues(clockValues, symbols, symbolValues)
  }

  def serialize: String = {
    def toBigJArray(array : Array[Big])  = JArray(array.toList.map { a ⇒ val v: JValue = a; v })

    val json =
      ("numberOfBuffers" -> numberOfBuffers) ~
      ("nextForData"     -> ("Big" -> data.size) ~ ("Int" -> 0) ~ ("Long" -> 0)) ~
      ("intData"         -> List()) ~
      ("longData"        -> List()) ~
      ("bigData"         -> toBigJArray(data)) ~
      ("rollbackData"    -> List())
    pretty(render(json))
  }
  def deserialize(jsonString: String): Unit = {
    val json2 = parse(jsonString)

    for {JObject(child) <- json2; JField(fieldName, value) <- child} {
      fieldName match {
        case "numberOfBuffers" =>
          val JInt(numBuffs) = value
          assert(numBuffs == 0, "simple.DataStore does not support any rollback buffers")
        case "nextForData" =>
          assert((value \ "Int" \\ classOf[JInt]).head.values == 0)
          assert((value \ "Long" \\ classOf[JInt]).head.values == 0)
          assert((value \ "Big" \\ classOf[JInt]).head.values == data.length)
        case "bigData" =>
          value match  {
            case JArray(elementValues) =>
              elementValues.zipWithIndex.foreach {
                case (JInt(v), index) => data(index) = v
                case _ => None
              }
            case _ =>
          }
        case _ =>
      }
    }
  }
}

object DataStore {
  def apply(allocator: DataStoreAllocator): DataStore = {
    new DataStore(allocator)
  }
}

class DataStoreAllocator {
  private var nextIndex : Int = 0
  def getSize : Int = nextIndex
  def getIndex(slots: Int = 1): Int = {
    val index = nextIndex
    nextIndex += slots
    index
  }
}
