package fol.semidecisionprocedures.modelfinder

import org.warthog.fol.formulas.{FOLPredicate, FOLFunction, FOLVariable}
import org.warthog.fol.semidecisionprocedures.modelfinder.{FOLLiteral, Clause,Modelfinder,CNF}
import org.specs2.mutable._
import org.warthog.pl.decisionprocedures.satsolver.impl.picosat.Picosat
import org.warthog.pl.decisionprocedures.satsolver.{Infinity, Solver, sat}
import org.warthog.pl.formulas.{PL, PLAtom}
import org.warthog.generic.formulas.{Formula, Or, Not}

/**
 * Created with IntelliJ IDEA.
 * User: Nebu
 * Date: 27.05.12
 * Time: 19:16
 * To change this template use File | Settings | File Templates.
 */

class modelfinderTester extends Specification{
val a = FOLFunction("a")
val b = FOLFunction("b")
val c = FOLFunction("c")
val x = FOLVariable("x")
val y = FOLVariable("y")
val z = FOLVariable("z")
val v = FOLVariable("v")
val f = FOLFunction("f",x,y)
val g = FOLFunction("g",x)
val h = FOLFunction("h",x,y,z)
val gxfxy = FOLLiteral(true,FOLPredicate("=",f,g))
val C = Clause(Set(gxfxy))
val fxy = FOLLiteral(true,FOLPredicate("=",f,x))
val notfxy = FOLLiteral(false,FOLPredicate("=",f,x))
val fxynotfxy = Clause(Set(fxy,notfxy))
val ps = new Picosat
var rv0: Int = _
val one = FOLFunction("1")
val two = FOLFunction("2")
val X1 =  FOLLiteral(true,FOLPredicate("=",x,one))
val X2 =  FOLLiteral(true,FOLPredicate("=",x,two))
val Y1 =  FOLLiteral(true,FOLPredicate("=",y,one))
val Y2 =  FOLLiteral(true,FOLPredicate("=",y,two))
val XY =  FOLLiteral(true,FOLPredicate("=",x,y))
val trueVerumLit = FOLLiteral(true,FOLPredicate("=",one,one))
val falseVerumLit = FOLLiteral(false,FOLPredicate("=",one,one))
val trueFalsumLit = FOLLiteral(true,FOLPredicate("=",one,two))
val falseFalsumLit = FOLLiteral(false,FOLPredicate("=",one,two))
val NOTX1 =  FOLLiteral(false,FOLPredicate("=",x,one))
val NOTX2 =  FOLLiteral(false,FOLPredicate("=",x,two))
val NOTY1 =  FOLLiteral(false,FOLPredicate("=",y,one))
val NOTY2 =  FOLLiteral(false,FOLPredicate("=",y,two))
val NOTXY =  FOLLiteral(false,FOLPredicate("=",y,x))
val cnf1 = CNF(Set(Clause(Set(X1)),Clause(Set(Y2))))
val cnf2 = CNF(Set(Clause(Set(X1)),Clause(Set(Y2)),Clause(Set(XY))))
val cnf3 = CNF(Set(Clause(Set(fxy)),Clause(Set(notfxy))))
val cnf4 = CNF(Set(Clause(Set(XY)),Clause(Set(NOTX1,NOTY2)),Clause(Set(NOTX2,NOTY1))))
val emptyClause = Clause(Set())
val emptyCNF = CNF(Set())
val CNFofEmptryClause = CNF(Set(emptyClause))
val P = FOLPredicate("P",x,y,z)
val Q = FOLPredicate("=",h,v)
val R = FOLPredicate("=",x,y)
val P2 = FOLPredicate("P",x,x,z)
val paradoxExample1 = Clause(Set(FOLLiteral(true,FOLPredicate("P",a,g))))
val paradoxExample2 = Clause(Set(FOLLiteral(false,FOLPredicate("P",a,g))))
val paradoxExample3 = Clause(Set(FOLLiteral(true,FOLPredicate("P",FOLFunction("f",a,b),FOLFunction("f",b,a)))))
val paradoxExample4 = Clause(Set(FOLLiteral(true,FOLPredicate("P",x,y)),FOLLiteral(true,FOLPredicate("Q",x,z))))






C.toString should {
   "have Variables a and b" in {
     C.getVariables must be equalTo Set(x,y)
   }
   "be flattend correctly" in {
     val v1 = FOLVariable("Variable1")
     val L = FOLLiteral(true,FOLPredicate("=",v1,g))
     val M = FOLLiteral(false,FOLPredicate("=",v1,f))
     val c = Clause(Set(L,M))
     C.clauseflatten must be equalTo c
   }
   "have Functions f and g" in {
     C.getFunctions.toSet must be equalTo Set(f.symbol,g.symbol)
   }
   "get flattend and mapped correctly" in {
     val v1 = FOLVariable("Variable1")
     val a1 = FOLFunction("c1")
     val L = FOLLiteral(true,FOLPredicate("=",a1,g))
     val M = FOLLiteral(false,FOLPredicate("=",a1,f))
     val c = Clause(Set(L,M))
     val Map1 = Map(v1->a1)
     C.clauseflatten.substitute(Map1) must be equalTo Some(c)
   }


}

fxynotfxy.toString should{
   "get flattend and instantiatet correctly" in {
     Modelfinder.reset()
     val atom1 = PLAtom("Atom1")
     val atomnot1 = Not[PL](atom1)

     val form = Or[PL](atom1,atomnot1)
     fxynotfxy.clauseflatten.translateToPL() must be equalTo form
   }


    "be satisfiable" in {
      Modelfinder.reset()
      val form = fxynotfxy.clauseflatten.translateToPL()
      //form.atoms
      sat(ps) {
        (solver: Solver) => {
          solver.add(form)
          rv0 = solver.sat(Infinity)
        }
      }
      rv0 must be equalTo (1)
    }
}

  cnf1.toString should{
    "be satisfiable" in {
      Modelfinder.reset()
      Modelfinder.main(cnf1,2,"-result")must be equalTo "Sat: Map(x -> 1, y -> 2)"
    }
  }

  cnf2.toString should{
    "be unsatisfiable" in {
      Modelfinder.reset()
      Modelfinder.main(cnf2,2,"-result")must be equalTo "UNSAT"
    }
  }

  cnf3.toString should{
    "be unsatisfiable" in {
      Modelfinder.reset()
      Modelfinder.main(cnf3,2,"-result")must be equalTo "UNSAT"
    }
  }

  cnf4.toString should{
    "be satisfiable" in {
      Modelfinder.reset()
      Modelfinder.main(cnf4,2,"-result")must be equalTo "Sat: Map(x -> 1, y -> 1)"
    }
  }

  emptyClause.toString should{
    "be flattend to itself" in{
      emptyClause.clauseflatten must be equalTo emptyClause
    }
    "be binarysplit to itself" in{
      emptyClause.binarySplit must be equalTo Set(emptyClause)
    }
    "be groundsplit to itself" in{
      emptyClause.splitGrounds must be equalTo Set(emptyClause)
    }

  }

  emptyCNF.toString should{
    "be flattend to itself" in{
      Modelfinder.runflatten(emptyCNF) must be equalTo emptyCNF
    }
    "be binarysplit to itself" in{
      Modelfinder.runBinarySplit(emptyCNF) must be equalTo emptyCNF
    }
    "be groundsplit to itself" in{
      Modelfinder.runSplitGrounds(emptyCNF) must be equalTo emptyCNF
    }
    "be satisfiable" in{
      Modelfinder.reset()
      Modelfinder.main(emptyCNF,2,"") must be equalTo "Sat: Map()"
    }

  }

  CNFofEmptryClause.toString should{
    "be flattend to itself" in{
      Modelfinder.runflatten(CNFofEmptryClause) must be equalTo CNFofEmptryClause
    }
    "be binarysplit to itself" in{
      Modelfinder.runBinarySplit(CNFofEmptryClause) must be equalTo CNFofEmptryClause
    }
    "be groundsplit to itself" in{
      Modelfinder.runSplitGrounds(CNFofEmptryClause) must be equalTo CNFofEmptryClause
    }
    "be unsatisfiable" in{
      Modelfinder.reset()
      Modelfinder.main(CNFofEmptryClause,2,"") must be equalTo "UNSAT"
    }

  }

  trueVerumLit.toString should{
    "be satisfiable" in{
      Modelfinder.reset()
      Modelfinder.main(CNF(Set(Clause(Set(trueVerumLit)))),2,"") must be equalTo "Sat: Map()"
    }
  }

  falseVerumLit.toString should{
    "be unsatisfiable" in{
      Modelfinder.reset()
      Modelfinder.main(CNF(Set(Clause(Set(falseVerumLit)))),2,"") must be equalTo "UNSAT"
    }
  }

  trueFalsumLit.toString should{
    "be unsatisfiable" in{
      Modelfinder.reset()
      Modelfinder.main(CNF(Set(Clause(Set(trueFalsumLit)))),2,"") must be equalTo "UNSAT"
    }
  }

  falseFalsumLit.toString should{
    "be satisfiable" in{
      Modelfinder.reset()
      Modelfinder.main(CNF(Set(Clause(Set(falseFalsumLit)))),2,"") must be equalTo "Sat: Map()"
    }
  }

  Clause(Set(FOLLiteral(true,P))).toString should{
    "be flattend to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(true,P))).clauseflatten must be equalTo Clause(Set(FOLLiteral(true,P)))
    }
  }

  Clause(Set(FOLLiteral(false,P))).toString should{
    "be flattend to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(false,P))).clauseflatten must be equalTo Clause(Set(FOLLiteral(false,P)))
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(false,P))).binarySplit must be equalTo Set(Clause(Set(FOLLiteral(false,P))))
    }
  }

  Clause(Set(FOLLiteral(true,Q))).toString should{
    "be flattend to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(true,Q))).clauseflatten must be equalTo Clause(Set(FOLLiteral(true,Q)))
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(true,Q))).binarySplit must be equalTo Set(Clause(Set(FOLLiteral(true,Q))))
    }

  }

  Clause(Set(FOLLiteral(false,Q))).toString should{
    "be flattend to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(false,Q))).clauseflatten must be equalTo Clause(Set(FOLLiteral(false,Q)))
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(false,Q))).binarySplit must be equalTo Set(Clause(Set(FOLLiteral(false,Q))))
    }
  }

  Clause(Set(FOLLiteral(true,R))).toString should{
    "be flattend to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(true,R))).clauseflatten must be equalTo Clause(Set(FOLLiteral(true,R)))
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(true,R))).binarySplit must be equalTo Set(Clause(Set(FOLLiteral(true,R))))
    }
  }

  Clause(Set(FOLLiteral(false,R))).toString should{
    "be flattend to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(false,R))).clauseflatten must be equalTo Clause(Set(FOLLiteral(false,R)))
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(false,R))).binarySplit must be equalTo Set(Clause(Set(FOLLiteral(false,R))))
    }
  }

  Clause(Set(FOLLiteral(false,R),FOLLiteral(true,P))).toString should{
    "be flattend to "+Clause(Set(FOLLiteral(true,P2))).toString in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(false,R),FOLLiteral(true,P))).clauseflatten must be equalTo Clause(Set(FOLLiteral(true,P2)))
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(false,R),FOLLiteral(true,P))).binarySplit must be equalTo Set(Clause(Set(FOLLiteral(false,R),FOLLiteral(true,P))))
    }
  }

  Clause(Set(FOLLiteral(true,R),FOLLiteral(true,P))).toString should{
    "be flattend to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(true,R),FOLLiteral(true,P))).clauseflatten must be equalTo Clause(Set(FOLLiteral(true,R),FOLLiteral(true,P)))
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      Clause(Set(FOLLiteral(true,R),FOLLiteral(true,P))).binarySplit must be equalTo Set(Clause(Set(FOLLiteral(true,R),FOLLiteral(true,P))))
    }
  }

  paradoxExample1.toString should{
    "be flattend correctly" in{
      Modelfinder.reset()
      val v1 = FOLVariable("Variable1")
      val v2 = FOLVariable("Variable2")
      val lit1 = FOLLiteral(false,FOLPredicate("=",v1,a))
      val lit2 = FOLLiteral(false,FOLPredicate("=",v2,g))
      val lit3 = FOLLiteral(true,FOLPredicate("P",v1,v2))
      val result = Clause(Set(lit1,lit2,lit3))
      paradoxExample1.clauseflatten must be equalTo result
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      paradoxExample1.binarySplit must be equalTo Set(paradoxExample1)
    }
    "be splitGrounds to itself" in{
      Modelfinder.reset()
      paradoxExample1.splitGrounds must be equalTo Set(paradoxExample1)
    }

  }
  paradoxExample2.toString should{
    "be flattend correctly" in{
      Modelfinder.reset()
      val v1 = FOLVariable("Variable1")
      val v2 = FOLVariable("Variable2")
      val lit1 = FOLLiteral(false,FOLPredicate("=",v1,a))
      val lit2 = FOLLiteral(false,FOLPredicate("=",v2,g))
      val lit3 = FOLLiteral(false,FOLPredicate("P",v1,v2))
      val result = Clause(Set(lit1,lit2,lit3))
      paradoxExample2.clauseflatten must be equalTo result
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      paradoxExample2.binarySplit must be equalTo Set(paradoxExample2)
    }
    "be splitGrounds to itself" in{
      Modelfinder.reset()
      paradoxExample2.splitGrounds must be equalTo Set(paradoxExample2)
    }
  }

  paradoxExample3.toString should{
    "be flattend correctly" in{
      Modelfinder.reset()
      val v1 = FOLVariable("Variable1")
      val v2 = FOLVariable("Variable2")
      val v3 = FOLVariable("Variable3")
      val v4 = FOLVariable("Variable4")
      val lit1 = FOLLiteral(false,FOLPredicate("=",v2,a))
      val lit2 = FOLLiteral(false,FOLPredicate("=",v3,b))
      val lit3 = FOLLiteral(false,FOLPredicate("=",v1,FOLFunction("f",v2,v3)))
      val lit4 = FOLLiteral(false,FOLPredicate("=",v4,FOLFunction("f",v3,v2)))
      val lit5 = FOLLiteral(true,FOLPredicate("P",v1,v4))
      val result = Clause(Set(lit1,lit2,lit3,lit4,lit5))
      paradoxExample3.clauseflatten must be equalTo result
    }
    "be binarySplit to itself" in{
      Modelfinder.reset()
      paradoxExample3.binarySplit must be equalTo Set(paradoxExample3)
    }
    "be splitGrounds correctly" in{
      Modelfinder.reset()
      val v1 = FOLVariable("Variable1")
      val v2 = FOLVariable("Variable2")
      val v3 = FOLVariable("Variable3")
      val v4 = FOLVariable("Variable4")
      val v5 = FOLVariable("Variable5")
      val v6 = FOLVariable("Variable6")
      val c1 = FOLFunction("Constant1")
      val c2 = FOLFunction("Constant2")
      val lit1 = FOLLiteral(false,FOLPredicate("=",v2,a))
      val lit2 = FOLLiteral(false,FOLPredicate("=",v3,b))
      val lit3 = FOLLiteral(false,FOLPredicate("=",v1,FOLFunction("f",v2,v3)))
      val lit4 = FOLLiteral(false,FOLPredicate("=",v4,FOLFunction("f",v3,v2)))
      val lit5 = FOLLiteral(true,FOLPredicate("=",v1,c1))
      val lit6 = FOLLiteral(true,FOLPredicate("=",v4,c2))
      val lit7 = FOLLiteral(true,FOLPredicate("P",v5,v6))
      val lit8 = FOLLiteral(false,FOLPredicate("=",v5,c1))
      val lit9 = FOLLiteral(false,FOLPredicate("=",v6,c2))
      val result = Set(Clause(Set(lit1,lit2,lit3,lit5)),Clause(Set(lit1,lit2,lit4,lit6)),Clause(Set(lit7,lit8,lit9)))
      paradoxExample3.splitGrounds.map(c=>c.clauseflatten) must be equalTo result
    }

    "be splitGrounds and then flattend correctly" in{
      Modelfinder.reset()
      val c1 = FOLFunction("Constant1")
      val c2 = FOLFunction("Constant2")
      val lit1 = FOLLiteral(true,FOLPredicate("=",FOLFunction("f",a,b),c1))
      val lit2 = FOLLiteral(true,FOLPredicate("=",FOLFunction("f",b,a),c2))
      val lit3 = FOLLiteral(true,FOLPredicate("P",c1,c2))
      val result = Set(Clause(Set(lit1)),Clause(Set(lit2)),Clause(Set(lit3)))
      paradoxExample3.splitGrounds must be equalTo result
    }


  }

  paradoxExample4.toString should{
    "be flattend to itself" in{
      Modelfinder.reset()
      paradoxExample4.clauseflatten must be equalTo paradoxExample4
    }
    "be binarySplit correctly" in{
      Modelfinder.reset()
      val pred1 = FOLPredicate("Predicate1",x)
      val lit1 = FOLLiteral(true,pred1)
      val lit2 = FOLLiteral(false,pred1)
      val clause1 = Clause(Set(FOLLiteral(true,FOLPredicate("P",x,y)),lit1))
      val clause2 = Clause(Set(lit2,FOLLiteral(true,FOLPredicate("Q",x,z))))
      paradoxExample4.binarySplit must be equalTo Set(clause1,clause2)
    }
    "be splitGrounds to itself" in{
      Modelfinder.reset()
      paradoxExample4.splitGrounds must be equalTo Set(paradoxExample4)
    }
  }






}
