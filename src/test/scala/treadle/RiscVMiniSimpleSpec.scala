// See LICENSE for license details.

package treadle

import firrtl.stage.FirrtlSourceAnnotation
import org.scalatest.{FreeSpec, Matchers}
import treadle.executable.{ClockInfo, FastExecutionBackend, SimpleExecutionBackend, StopException}

//scalastyle:off magic.number
class RiscVMiniSimpleSpec extends FreeSpec with Matchers {
  val stream = getClass.getResourceAsStream("/core-simple.lo.fir")
  val input = scala.io.Source.fromInputStream(stream).getLines().mkString("\n")
  val annos = Seq(
    FirrtlSourceAnnotation(input),
    ClockInfoAnnotation(Seq(ClockInfo("clock", period = 10, initialOffset = 1)))
  )
  private def test(tester: TreadleTester) = {
    intercept[StopException] {
      tester.step(400)
    }
    tester.report()
    tester.engine.lastStopResult should be(Some(0))
  }

  "riscv-mini simple core test should run then stop" in {
    test(TreadleTester(annos ++ Seq(TreadleBackendAnnotation(FastExecutionBackend))))
  }

  "riscv-mini simple core test should run then stop with SimpleExecutionBackend" in {
    test(TreadleTester(annos ++ Seq(TreadleBackendAnnotation(SimpleExecutionBackend))))
  }
}
