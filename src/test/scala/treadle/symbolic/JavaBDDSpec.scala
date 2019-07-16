// See LICENSE for license details.

package treadle.symbolic

import org.scalatest.{Matchers, FreeSpec}
import net.sf.javabdd.{BDD, BDDDomain, BDDException, JFactory}

//scalastyle:off magic.number
class JavaBDDSpec extends FreeSpec with Matchers {

  "JavaBDD should correctly support zeros and ones" in {
    val bdd = JFactory.init(10, 10)
    val x = bdd.zero
    val y = bdd.one
    if (bdd.varNum < 5) { bdd.setVarNum(5) }
    val z = bdd.ithVar(1)

    x.isZero should be (true)
    x.isOne should be (false)
    y.isZero should be (false)
    y.isOne should be (true)
    z.isZero should be (false)
    z.isOne should be (false)

    Seq(x, y, z).foreach { _.free() }
    bdd.done()
  }

  "add 'axiom' to make formula unsat" in {
    val bdd = JFactory.init(10, 10)
    if (bdd.varNum < 5) { bdd.setVarNum(5) }
    val a = bdd.ithVar(0)
    val b = bdd.ithVar(1)
    val all_vars = a.and(b)

    val phi = a.and(b)
    val axiom = a.xor(b)

    val result = phi.and(axiom)

    phi.isOne   || phi.isZero   should be (false)
    axiom.isOne || axiom.isZero should be (false)
    result.isOne  should be (false)
    result.isZero should be (true)

    // get one result
    phi.satCount(all_vars) should be (1.0)
    axiom.satCount(all_vars) should be (2.0)
    result.satCount(all_vars) should be (0.0)

    bdd.done()
  }

  //"JavaBDD should support s"
}
