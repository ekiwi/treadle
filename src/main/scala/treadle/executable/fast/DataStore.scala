// See LICENSE for license details.

package treadle.executable.fast

import firrtl.ir.Info
import org.json4s._
import org.json4s.native.JsonMethods._
import org.json4s.JsonDSL._
import treadle.ScalaBlackBox
import treadle.executable._

import scala.collection.mutable

/**
  * Creates a data store for the three underlying data types.
  * The numberOfBuffers is used to control the ability to rollback execution.
  * The meaning of the values of each slot must be maintained outside of this class.
  * This class only supports (2 ** 31) - 1 of any ints, longs or bigs.
  *
  * @param numberOfBuffers Number of buffers
  */
//scalastyle:off number.of.methods
class DataStore(val numberOfBuffers: Int, dataStoreAllocator: DataStoreAllocator)
extends HasDataArrays with AbstractDataStore {
  assert(numberOfBuffers >= 0, s"DataStore: numberOfBuffers $numberOfBuffers must be >= 0")

  def numberOfInts: Int  = dataStoreAllocator.nextIndexFor(IntSize)
  def numberOfLongs: Int = dataStoreAllocator.nextIndexFor(LongSize)
  def numberOfBigs: Int  = dataStoreAllocator.nextIndexFor(BigSize)

  val intData:   Array[Int]  = Array.fill(numberOfInts)(0)
  val longData:  Array[Long] = Array.fill(numberOfLongs)(0L)
  val bigData:   Array[Big]  = Array.fill(numberOfBigs)(Big(0))

  val rollBackBufferManager = new RollBackBufferManager(numberOfBuffers, new RollBackBuffer(this))

  def findBufferBeforeClockTransition(time: Long, clock: Symbol, prevClock: Symbol): Option[DataBuffer] =
    rollBackBufferManager.findBufferBeforeClockTransition(time, clock, prevClock)

  def saveData(time: Long): Unit = {
    if(numberOfBuffers > 0) {
      rollBackBufferManager.saveData(time)
    }
  }

  @deprecated("Use saveData(time: Long), clock based rollback buffers are no longer supported", "since 1.0")
  def saveData(clockName: String, time: Long): Unit = {
    if(numberOfBuffers > 0) {
      rollBackBufferManager.saveData(time)
    }
  }

  def runPlugins(symbol: Symbol, offset: Int = -1): Unit = {
    activePlugins.foreach { _.run(symbol, offset) }
  }

def makeConstantAssigner(symbol: Symbol, value: Big, info: Info) : Assigner = {
    symbol.dataSize match {
      case IntSize  => AssignInt(symbol,  GetIntConstant(value.toInt).apply _, info)
      case LongSize => AssignLong(symbol, GetLongConstant(value.toLong).apply _, info)
      case BigSize  => AssignBig(symbol,  GetBigConstant(value).apply _, info)
    }
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
      val value = if( symbol.forcedValue.isDefined) { symbol.forcedValue.get.toInt } else { expression() }
      intData(index) = value
      runPlugins(symbol)
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean _ else runFull _
    }
    var run: FuncUnit = runLean _
  }

  case class ExternalModuleInputAssigner(
    symbol:             Symbol,
    portName:           String,
    blackBox:           ScalaBlackBox,
    underlyingAssigner: Assigner
  ) extends Assigner {

    val info: Info = underlyingAssigner.info

    override def run: FuncUnit = {
      underlyingAssigner.run()
      blackBox.inputChanged(portName, apply(symbol))
      () => Unit
    }
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
      val value = if( symbol.forcedValue.isDefined) { symbol.forcedValue.get.toLong } else { expression() }

      longData(index) = value
      runPlugins(symbol)
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean _ else runFull _
    }
    var run: FuncUnit = runLean _
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
      val value = if( symbol.forcedValue.isDefined) { symbol.forcedValue.get } else { expression() }

      bigData(index) = value
      runPlugins(symbol)
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean _ else runFull _
    }
    var run: FuncUnit = runLean _
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
        val value = if( symbol.forcedValue.isDefined) { symbol.forcedValue.get.toInt } else { expression() }

        val memoryIndex = getMemoryIndex.apply()
        intData(index + (memoryIndex % memorySymbol.slots)) = value
        runPlugins(memorySymbol, memoryIndex)
      }
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean _ else runFull _
    }
    var run: FuncUnit = runLean _
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
        val value = if( symbol.forcedValue.isDefined) { symbol.forcedValue.get.toLong } else { expression() }

        val memoryIndex = getMemoryIndex.apply()
        longData(index + (memoryIndex % memorySymbol.slots)) = value
        runPlugins(memorySymbol, memoryIndex)
      }
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean _ else runFull _
    }
    var run: FuncUnit = runLean _
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
        val value = if( symbol.forcedValue.isDefined) { symbol.forcedValue.get } else { expression() }

        val memoryIndex = getMemoryIndex.apply()
        bigData(index + (memoryIndex % memorySymbol.slots)) = value
        runPlugins(memorySymbol, memoryIndex)
      }
    }

    override def setLeanMode(isLean: Boolean): Unit = {
      run = if(isLean) runLean _ else runFull _
    }
    var run: FuncUnit = runLean _
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

  def getWaveformValues(symbols: Array[Symbol], startCycle: Int = 0, endCycle: Int = -1): WaveformValues = {
    var buffers: Seq[RollBackBuffer] = rollBackBufferManager.newestToOldestBuffers.reverse

    val leftIndexInclusive = math.max(0, startCycle)
    val rightIndexExclusive = if (endCycle == -1) buffers.length else math.min(buffers.length, endCycle)
    val n = rightIndexExclusive - leftIndexInclusive

    buffers = buffers.dropRight(buffers.length - rightIndexExclusive).drop(leftIndexInclusive)

    val clockValues = new Array[BigInt](n)
    val symbolValues = Array.ofDim[BigInt](symbols.length, n)

    buffers.zipWithIndex.foreach { case (buffer, i) =>
      clockValues(i) = buffer.getTime
      symbols.zipWithIndex.foreach { case (symbol, j) =>
        symbol.dataSize match {
          case IntSize => symbolValues(j)(i) = buffer.intData(symbol.index)
          case LongSize => symbolValues(j)(i) = buffer.longData(symbol.index)
          case BigSize => symbolValues(j)(i) = buffer.bigData(symbol.index)
        }
      }
    }
    WaveformValues(clockValues, symbols, symbolValues)
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
      val packet = List("AllClocks").map { clockName =>
        val rollbackRing = rollBackBufferManager.rollBackBufferRing

        val intArray  = JArray(rollbackRing.ringBuffer.map { x => toIntJArray(x.intData)   }.toList)
        val longArray = JArray(rollbackRing.ringBuffer.map { x => toLongJArray(x.longData) }.toList)
        val bigArray  = JArray(rollbackRing.ringBuffer.map { x => toBigJArray(x.bigData)   }.toList)

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
          var clockBuffer = rollBackBufferManager.rollBackBufferRing
          value match {
            case JArray(clockSections) =>
              for {
                JObject(child2) <- clockSections
                JField(subFieldName, subValue) <- child2
              } {
                (subFieldName, subValue) match {
                  case ("clockName", JString(clockName)) =>
                    clockBuffer = rollBackBufferManager.rollBackBufferRing

                  case ("latestBufferIndex", JInt(latestBufferIndex)) =>
                    clockBuffer.latestBufferIndex = latestBufferIndex.toInt

                  case ("oldestBufferIndex", JInt(oldestBufferIndex)) =>
                    clockBuffer.oldestBufferIndex = oldestBufferIndex.toInt

                  case ("intBuffers", JArray(numArrays)) =>
                    numArrays.zipWithIndex.foreach {
                      case (JArray(elementValues), rollbackIndex) =>
                        elementValues.zipWithIndex.foreach {
                          case (JInt(v), index) =>
                            clockBuffer.ringBuffer(rollbackIndex).intData(index) = v.toInt
                          case _ => None
                        }
                      case _ =>
                    }

                  case ("longBuffers", JArray(numArrays)) =>
                    numArrays.zipWithIndex.foreach {
                      case (JArray(elementValues), rollbackIndex) =>
                        elementValues.zipWithIndex.foreach {
                          case (JInt(v), index) =>
                            clockBuffer.ringBuffer(rollbackIndex).longData(index) = v.toLong
                          case _ => None
                        }
                      case _ =>
                    }

                  case ("bigBuffers", JArray(numArrays)) =>
                    numArrays.zipWithIndex.foreach {
                      case (JArray(elementValues), rollbackIndex) =>
                        elementValues.zipWithIndex.foreach {
                          case (JInt(v), index) =>
                            clockBuffer.ringBuffer(rollbackIndex).bigData(index) = v
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

object DataStore {
  def apply(numberOfBuffers: Int, dataStoreAllocator: DataStoreAllocator): DataStore = {
    new DataStore(numberOfBuffers, dataStoreAllocator)
  }
}

trait HasDataArrays extends DataReader {
  def intData  : Array[Int]
  def longData : Array[Long]
  def bigData  : Array[Big]
  
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
}

class DataStoreAllocator {
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

/**
  * [[DataBuffer]] implementation for the default [[DataStore]].
  * @param dataStore the dataStore to be backed up.
  */
class RollBackBuffer(dataStore: DataStore) extends HasDataArrays with DataBuffer {
  private var time: Long = 0L
  override def getTime: Long = time

  val intData    : Array[Int]  = Array.fill(dataStore.numberOfInts)(0)
  val longData   : Array[Long] = Array.fill(dataStore.numberOfLongs)(0)
  val bigData    : Array[Big]  = Array.fill(dataStore.numberOfBigs)(0)

  def dump(dumpTime: Long): Unit = {
    time = dumpTime
    Array.copy(dataStore.intData,  0, intData,  0, intData.length)
    Array.copy(dataStore.longData, 0, longData, 0, longData.length)
    Array.copy(dataStore.bigData,  0, bigData,  0, bigData.length)
  }
}
