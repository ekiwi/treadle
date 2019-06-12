// See LICENSE for license details.
package treadle

import org.scalatest.{FlatSpec, Matchers}

// scalastyle:off magic.number

class SymbolicGCDTester extends FlatSpec with Matchers {
  behavior of "Symbolic GCD"

  val gcdFirrtl: String =
    s"""
    |circuit GCD :
    |  module GCD :
    |    input clock : Clock
    |    input reset : UInt<1>
    |    input io_a : UInt<32>
    |    input io_b : UInt<32>
    |    input io_e : UInt<1>
    |    output io_z : UInt<32>
    |    output io_v : UInt<1>
    |    reg x : UInt<32>, clock with :
    |      reset => (UInt<1>("h0"), x)
    |    reg y : UInt<32>, clock with :
    |      reset => (UInt<1>("h0"), y)
    |    node T_13 = gt(x, y)
    |    node T_14 = sub(x, y)
    |    node T_15 = tail(T_14, 1)
    |    node T_17 = eq(T_13, UInt<1>("h0"))
    |    node T_18 = sub(y, x)
    |    node T_19 = tail(T_18, 1)
    |    node T_21 = eq(y, UInt<1>("h0"))
    |    node GEN_0 = mux(T_13, T_15, x)
    |    x <= mux(io_e, io_a, GEN_0)
    |    node GEN_1 = mux(T_17, T_19, y)
    |    y <= mux(io_e, io_b, GEN_1)
    |    io_z <= x
    |    io_v <= T_21
  """.stripMargin

  it should "run with TreadleTester" in {

    val manager = new TreadleOptionsManager {
      treadleOptions = treadleOptions.copy(
        rollbackBuffers = 0, showFirrtlAtLoad = false, setVerbose = false, writeVCD = false)
    }

    val tester = TreadleTester(gcdFirrtl, manager)

    List((1, 1, 1), (34, 17, 17), (8, 12, 4)).foreach { case (x, y, z) =>
      tester.step()
      tester.poke("io_a", x)
      tester.poke("io_b", y)
      tester.poke("io_e", 1)
      tester.step()

      tester.poke("io_e", 0)
      tester.step()

      while (tester.peek("io_v") != Big1) {
        tester.step()
      }
      tester.expect("io_z", z)
    }
  }
}
