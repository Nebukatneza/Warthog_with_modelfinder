package fol.semidecisionprocedures.modelfinder

import org.specs2.mutable.Specification
import org.warthog.fol.semidecisionprocedures.modelfinder.{FOLLiteral, Clause,Modelfinder,CNF,TPTPParser}
import org.warthog.fol.formulas.{FOLPredicate, FOLFunction, FOLVariable}


/**
 * Created with IntelliJ IDEA.
 * User: Nebu
 * Date: 19.07.12
 * Time: 18:00
 * To change this template use File | Settings | File Templates.
 */

class TPTPParserTester extends Specification{

  val test1 = "L:/Bachelor/test1.ax"
  val a = FOLFunction("a")
  val b = FOLFunction("b")
  val f = FOLFunction("f",b)
  val P = FOLPredicate("p",a,f)
  val cnf1 = CNF(Set(Clause(Set(FOLLiteral(true,P)))))

  test1 should{
    "be interpreted correctly" in {
      TPTPParser.interpredProblem(test1) must be equalTo cnf1
    }
    "be sat" in{
      Modelfinder.run(TPTPParser.interpredProblem(test1),2) must be equalTo "Sat"
    }
  }



}
