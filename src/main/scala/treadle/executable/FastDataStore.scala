// See LICENSE for license details.

package treadle.executable

import firrtl.ir.Info
import org.json4s._
import org.json4s.native.JsonMethods._
import org.json4s.JsonDSL._
import treadle.utils.Render

import scala.collection.mutable


/**
  * Creates a data store for the three underlying data types.
  * The numberOfBuffers is used to control the ability to rollback execution.
  * The meaning of the values of each slot must be maintained outside of this class.
  * This class only supports (2 ** 31) - 1 of any ints, longs or bigs.
  *
  * @param numberOfBuffers Number of buffers
  */
class FastDataStore(numberOfBuffers: Int, dataStoreAllocator: FastDataStoreAllocator)
    extends DataStore(numberOfBuffers) {
  override def makeRollBackBuffer() : RollBackBuffer = new FastRollBackBuffer(this)

  def numberOfInts: Int  = dataStoreAllocator.nextIndexFor(IntSize)
  def numberOfLongs: Int = dataStoreAllocator.nextIndexFor(LongSize)
  def numberOfBigs: Int  = dataStoreAllocator.nextIndexFor(BigSize)

  val intData:   Array[Int]  = Array.fill(numberOfInts)(0)
  val longData:  Array[Long] = Array.fill(numberOfLongs)(0L)
  val bigData:   Array[Big]  = Array.fill(numberOfBigs)(Big(0))

  def setValueAtIndex(dataSize: DataSize, index: Int, value: Big): Unit = {
    dataSize match {
      case IntSize  => intData(index)  = value.toInt
      case LongSize => longData(index) = value.toLong
      case BigSize  => bigData(index)  = value
    }
  }

  def getValueAtIndex(dataSize: DataSize, index: Int): BigInt = {
    dataSize match {
      case IntSize  => intData(index)
      case LongSize => longData(index)
      case BigSize  => bigData(index)
    }
  }

  override def makeConstantAssigner(symbol: Symbol, const: Big, info: Info) : Assigner = {
    val cc = symbol.valueFrom(const)
    symbol.dataSize match {
      case IntSize  => AssignInt( symbol, GetIntConstant(cc.toInt).apply, info)
      case LongSize => AssignLong(symbol, GetLongConstant(cc.toLong).apply, info)
      case BigSize  => AssignBig( symbol, GetBigConstant(cc).apply, info)
    }
  }

  override def getSymbolFilterFromGetter(expressionResult: ExpressionResult): Option[Symbol => Boolean] = {
    expressionResult match {
      case GetInt(index)  => Some({ symbol : Symbol => symbol.dataSize == IntSize && symbol.index == index})
      case GetLong(index) => Some({ symbol : Symbol => symbol.dataSize == LongSize && symbol.index == index})
      case GetBig(index)  => Some({ symbol : Symbol => symbol.dataSize == BigSize && symbol.index == index})
      case _ => None
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
  def serialize: String = {

    val nextForData = Seq(IntSize, LongSize, BigSize).map { size =>
      size.toString -> dataStoreAllocator.nextIndexFor(size)
    }.toMap

    def toIntJArray(array : Array[Int])  = JArray(array.toList.map { a ⇒ val v: JValue = a; v })
    def toLongJArray(array: Array[Long]) = JArray(array.toList.map { a ⇒ val v: JValue = a; v })
    def toBigJArray(array : Array[Big])  = JArray(array.toList.map { a ⇒ val v: JValue = a; v })

    val intDataValues  = toIntJArray(intData)
    val longDataValues = toLongJArray(longData)
    val bigDataValues  = toBigJArray(bigData)

    def packageRollbackBuffers = {
      val packet = rollBackBufferManager.clockToBuffers.keys.toList.sorted.map { clockName =>
        val rollbackRing = rollBackBufferManager.clockToBuffers(clockName)

        val intArray  = JArray(rollbackRing.ringBuffer.map{ case x: FastRollBackBuffer => toIntJArray(x.intData) }.toList)
        val longArray = JArray(rollbackRing.ringBuffer.map{ case x: FastRollBackBuffer => toLongJArray(x.longData) }.toList)
        val bigArray  = JArray(rollbackRing.ringBuffer.map{ case x: FastRollBackBuffer => toBigJArray(x.bigData)   }.toList)

        ("clockName" -> clockName) ~
            ("latestBufferIndex" -> rollbackRing.latestBufferIndex) ~
            ("oldestBufferIndex" -> rollbackRing.oldestBufferIndex) ~
            ("intBuffers"        -> intArray) ~
            ("longBuffers"       -> longArray) ~
            ("bigBuffers"        -> bigArray)
      }

      packet
    }

    val json =
      ("numberOfBuffers" -> numberOfBuffers) ~
          ("nextForData"     -> nextForData) ~
          ("intData"         -> intDataValues) ~
          ("longData"        -> longDataValues) ~
          ("bigData"         -> bigDataValues) ~
          ("rollbackData"    -> packageRollbackBuffers)

    pretty(render(json))
  }

  def deserialize(jsonString: String): Unit = {
    val json2 = parse(jsonString)

    for {
      JObject(child) <- json2
      JField(fieldName, value) <- child
    } {
      fieldName match {
        case "numberOfBuffers" =>
          val JInt(numBuffs) = value
          if(numBuffs != numberOfBuffers) {
            println(s"WARNING: numberOfBuffers in snapshot $numBuffs does not match runtime $numberOfBuffers")
          }
        case "nextForData" =>
          for {
            JObject(child2) <- value
            JField(fieldName, value) <- child2
          } {
            val JInt(nextNumber) = value
            fieldName match {
              case "Int"  => dataStoreAllocator.nextIndexFor(IntSize)  = nextNumber.toInt
              case "Long" => dataStoreAllocator.nextIndexFor(LongSize) = nextNumber.toInt
              case "Big"  => dataStoreAllocator.nextIndexFor(BigSize)  = nextNumber.toInt
            }
          }
        case "intData" =>
          value match  {
            case JArray(elementValues) =>
              elementValues.zipWithIndex.foreach {
                case (JInt(v), index) => intData(index) = v.toInt
                case _ => None
              }
            case _ =>
          }
        case "longData" =>
          value match  {
            case JArray(elementValues) =>
              elementValues.zipWithIndex.foreach {
                case (JInt(v), index) => longData(index) = v.toLong
                case _ => None
              }
            case _ =>
          }
        case "bigData" =>
          value match  {
            case JArray(elementValues) =>
              elementValues.zipWithIndex.foreach {
                case (JInt(v), index) => bigData(index) = v
                case _ => None
              }
            case _ =>
          }
        case "rollbackData" =>
          var clockBuffer = rollBackBufferManager.clockToBuffers.values.head
          value match {
            case JArray(clockSections) =>
              for {
                JObject(child2) <- clockSections
                JField(subFieldName, subValue) <- child2
              } {
                (subFieldName, subValue) match {
                  case ("clockName", JString(clockName)) =>
                    assert(rollBackBufferManager.clockToBuffers.contains(clockName))
                    clockBuffer = rollBackBufferManager.clockToBuffers(clockName)

                  case ("latestBufferIndex", JInt(latestBufferIndex)) =>
                    clockBuffer.latestBufferIndex = latestBufferIndex.toInt

                  case ("oldestBufferIndex", JInt(oldestBufferIndex)) =>
                    clockBuffer.oldestBufferIndex = oldestBufferIndex.toInt

                  case ("intBuffers", JArray(numArrays)) =>
                    numArrays.zipWithIndex.foreach {
                      case (JArray(elementValues), rollbackIndex) =>
                        elementValues.zipWithIndex.foreach {
                          case (JInt(v), index) =>
                            clockBuffer.ringBuffer(rollbackIndex).asInstanceOf[FastRollBackBuffer].intData(index) = v.toInt
                          case _ => None
                        }
                      case _ =>
                    }

                  case ("longBuffers", JArray(numArrays)) =>
                    numArrays.zipWithIndex.foreach {
                      case (JArray(elementValues), rollbackIndex) =>
                        elementValues.zipWithIndex.foreach {
                          case (JInt(v), index) =>
                            clockBuffer.ringBuffer(rollbackIndex).asInstanceOf[FastRollBackBuffer].longData(index) = v.toLong
                          case _ => None
                        }
                      case _ =>
                    }

                  case ("bigBuffers", JArray(numArrays)) =>
                    numArrays.zipWithIndex.foreach {
                      case (JArray(elementValues), rollbackIndex) =>
                        elementValues.zipWithIndex.foreach {
                          case (JInt(v), index) =>
                            clockBuffer.ringBuffer(rollbackIndex).asInstanceOf[FastRollBackBuffer].bigData(index) = v
                          case _ => None
                        }
                      case _ =>
                    }

                  case (subSubFieldName, subSubValue) =>
                    println(s"got an unhandled field in clock buffer section $subSubFieldName => $subSubValue")
                }
              }

            case _ =>
          }

        case _ =>
        // println(s"$fieldName -> $value")
      }
    }
  }

}

class FastDataStoreAllocator extends DataStoreAllocator {
  val nextIndexFor = new mutable.HashMap[DataSize, Int]

  nextIndexFor(IntSize)  = 0
  nextIndexFor(LongSize) = 0
  nextIndexFor(BigSize)  = 0

  def numberOfInts: Int  = nextIndexFor(IntSize)
  def numberOfLongs: Int = nextIndexFor(LongSize)
  def numberOfBigs: Int  = nextIndexFor(BigSize)

  val watchList: mutable.HashSet[Symbol] = new mutable.HashSet()

  def getSizes: (Int, Int, Int) = {
    (nextIndexFor(IntSize), nextIndexFor(LongSize), nextIndexFor(BigSize))
  }

  def getIndex(dataSize: DataSize, slots: Int = 1): Int = {
    val index = nextIndexFor(dataSize)
    nextIndexFor(dataSize) += slots
    index
  }
}

class FastRollBackBuffer(dataStore: FastDataStore) extends RollBackBuffer {
  var time: Long = 0L

  val intData    : Array[Int]  = Array.fill(dataStore.numberOfInts)(0)
  val longData   : Array[Long] = Array.fill(dataStore.numberOfLongs)(0)
  val bigData    : Array[Big]  = Array.fill(dataStore.numberOfBigs)(0)

  def getValueAtIndex(dataSize: DataSize, index: Int): BigInt = {
    dataSize match {
      case IntSize  => intData(index)
      case LongSize => longData(index)
      case BigSize  => bigData(index)
    }
  }

  def dump(dumpTime: Long): Unit = {
    time = dumpTime
    Array.copy(dataStore.intData,  0, intData,  0, intData.length)
    Array.copy(dataStore.longData, 0, longData, 0, longData.length)
    Array.copy(dataStore.bigData,  0, bigData,  0, bigData.length)
  }
}

object FastDataStore {
  def apply(numberOfBuffers: Int, dataStoreAllocator: FastDataStoreAllocator): FastDataStore = {
    new FastDataStore(numberOfBuffers, dataStoreAllocator)
  }
  def allocator(): FastDataStoreAllocator = new FastDataStoreAllocator
}