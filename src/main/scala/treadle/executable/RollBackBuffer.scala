// See LICENSE for license details.

package treadle.executable

import scala.collection.mutable

trait RollBackBuffer extends DataStoreReader {
  var time: Long
  def dump(dumpTime: Long): Unit
}

class RollBackBufferRing(dataStore: DataStore) {
  val numberOfBuffers: Int = dataStore.numberOfBuffers
  val ringBuffer: Array[RollBackBuffer] = Array.fill(dataStore.numberOfBuffers)(dataStore.makeRollBackBuffer())

  var oldestBufferIndex: Int = 0
  var latestBufferIndex: Int = 0

  def currentNumberOfBuffers: Int = (latestBufferIndex + numberOfBuffers - oldestBufferIndex) % numberOfBuffers

  def newestToOldestBuffers: Seq[RollBackBuffer] = {
    var list = List.empty[RollBackBuffer]
    var index = latestBufferIndex
    while(index != oldestBufferIndex) {
      list = list :+ ringBuffer(index)
      index -= 1
      if(index < 0) {
        index = numberOfBuffers - 1
      }
    }
    list
  }

  def advanceAndGetNextBuffer(): RollBackBuffer = {
    latestBufferIndex += 1
    if(latestBufferIndex >= numberOfBuffers) {
      latestBufferIndex = 0
    }
    if(latestBufferIndex == oldestBufferIndex) {
      oldestBufferIndex += 1
      if(oldestBufferIndex >= numberOfBuffers) {
        oldestBufferIndex = 0
      }
    }
    ringBuffer(latestBufferIndex)
  }
}

/**
  * Manage a number of rollback buffers for each clock
  */
class RollBackBufferManager(dataStore: DataStore) {

  val clockToBuffers: mutable.HashMap[String, RollBackBufferRing] = new mutable.HashMap()

  def saveData(clockName: String, time: Long): Unit = {
    val buffer: RollBackBuffer = {
      if(! clockToBuffers.contains(clockName)) {
        clockToBuffers(clockName) = new RollBackBufferRing(dataStore)
      }
      clockToBuffers(clockName).advanceAndGetNextBuffer()
    }
    buffer.dump(time)
  }

  def findEarlierBuffer(clockName: String, time: Long): Option[RollBackBuffer] = {
    clockToBuffers.get(clockName) match {
      case Some(rollBackBufferRing) =>
        rollBackBufferRing.newestToOldestBuffers.find { buffer =>
          buffer.time < time
        }
      case _ =>
        None
    }
  }
}
