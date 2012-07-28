package pl.knowledgecompilation.dnnf

import org.warthog.generic.formulas.Formula
import org.warthog.pl.formulas.PL
import org.warthog.pl.knowledgecompilation.dnnf._
import org.warthog.pl.parsers._
import pl.F
import org.specs2.mutable._
import org.specs2.specification._
import org.warthog.pl.decisionprocedures.satsolver.impl.picosat.Picosat


/**
 * Tests for DNNF-Compilation and Operations
 *
 * Author: hildebrandt
 * Date:
 */

class DNNFCompilationTests extends Specification {

  val ps = new Picosat

  args(sequential = true)

  def compileT(f: Formula[PL], dnnf: DNNF): Fragments =
    "Compilation of " + f should {
      ("return " + dnnf + " using the Simple Compiler") in {
        compile(Simple, f) must be equalTo dnnf
      }
      ("return " + dnnf + " using the Advanced Compiler") in {
        compile(Advanced, f) must be equalTo dnnf
      }
    }

  def picoCheck(f: Formula[PL]): Fragments =
    "Checking equality of " + f + " and its compiled DNNF using Picosat" should {
      ("return true using the Simple Compiler") in {
        checkEquality(f, compile(Simple, f), ps) must be greaterThan 0
      }
      ("return true using the Advanced Compiler") in {
        checkEquality(f, compile(Advanced, f), ps) must be greaterThan 0
      }
    }


  compileT(F.x.pl, StringLit("x", true))
  compileT(F.notx.pl, StringLit("x", false))
  compileT(F.xy.pl, And(StringLit("x", true), StringLit("y", true)))
  compileT(F.xoy.pl, Or(StringLit("x", true), And(StringLit("x", false), StringLit("y", true))))

  picoCheck(F.verum.pl)
  picoCheck(F.falsum.pl)
  picoCheck(F.x.pl)
  picoCheck(F.notx.pl)
  picoCheck(F.xy.pl)
  picoCheck(F.xoy.pl)
  picoCheck(F.n_xynz.pl)
  picoCheck(F.n_nxoyoz.pl)
  picoCheck(F.equiv1.pl)
  picoCheck(F.impl1_br.pl)
  picoCheck(F.impl1vv.pl)
  picoCheck(F.nxoyoz.pl)
  picoCheck(F.xyoz_br.pl)
  picoCheck(F.xorequiv1_br.pl)
}
