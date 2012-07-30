package org.warthog.fol.semidecisionprocedures.modelfinder

import collection.immutable.Map
import org.warthog.fol.formulas._
import collection.mutable.HashMap
import collection.mutable.HashSet
import org.warthog.pl.formulas.PL
import org.warthog.generic.formulas._
import scala.util.Random
import org.warthog.pl.decisionprocedures.satsolver.{sat, Infinity, Solver}
import org.warthog.pl.decisionprocedures.satsolver.impl.picosat.Picosat
import org.warthog.fol.formulas.FunctionSymbol
import org.warthog.fol.formulas.FOLVariable

object Modelfinder{
  var predhash:HashMap[FOLPredicate,Atom[PL]]=HashMap()
  var predhashreverse:HashMap[Atom[PL],FOLPredicate]=HashMap()
  var varhash:HashMap[FOLFunction,FOLVariable]=HashMap()
  var variableName = "Variable"
  var predicateName = "Predicate"
  var predcounter = 0
  var literals = Set[FOLLiteral]()
  var constantName = "Constant"
  var constantHash:HashMap[FOLFunction,FOLFunction]=HashMap()


  def test():CNF={
    val a = FOLFunction("a")
    val b = FOLFunction("b")
    val c = FOLFunction("c")
    val d = FOLFunction("d")
    val e = FOLFunction("e")
    val f = FOLFunction("f",b,a)
    val g = FOLFunction("f",a,b)
    val eins = FOLFunction("1")
    val zwei = FOLFunction("2")
    val x = FOLVariable("x")
    val y = FOLVariable("y")
    val z = FOLVariable("z")
    val v = FOLVariable("v")
    val w = FOLVariable("w")
    val L =  FOLLiteral(true,FOLPredicate("=",x,y))
    val M =  FOLLiteral(true,FOLPredicate("Q",x,y,z))
    val N =  FOLLiteral(true,FOLPredicate("R",d,f))
    val O =  FOLLiteral(true,FOLPredicate("O",a,d))
    val P =  FOLLiteral(true,FOLPredicate("P",f,x))
    val K =  FOLLiteral(true,FOLPredicate("=",y,eins))
    val C = Clause(Set(L))
    val cnf = CNF(Set(Clause(Set(P))))//,Clause(Set(N)),Clause(Set(O)),Clause(Set(P)),Clause(Set(K))))

    return cnf
  }


  def reset(){
    this.predhash=HashMap()
    this.predhashreverse=HashMap()
    this.varhash=HashMap()
    this.variableName = "Variable"
    this.predcounter = 0
    this.predicateName = "Predicate"
    this.constantName = "Constant"
    this.constantHash=HashMap()
  }


  /**
   * Runs the Modelfinder (main method)
   * @param cnf
   * @param domain
   * @return INT, result of the picosat-solver
   */


  def main(cnf:CNF,domain:Int):String={
    val t0 = System.nanoTime : Double
    val result = run(cnf,domain)
    val t1 = System.nanoTime : Double
    val viewableResult = interpredResult(result)
    return ((t1-t0)/1000000).toString+"ms\n"+ viewableResult
  }

  def interpredResult(maybeclauseset:Option[Set[Clause]]):String={
      if(maybeclauseset.isEmpty)
        return "UNSAT"
      val result = interpredPredicateAndFunctionResults(maybeclauseset.get)
    return result
  }

  def interpredPredicateAndFunctionResults(clauseset:Set[Clause]):String={
    var result = ""
    if (clauseset.isEmpty)
        return result
      if (Clause.predicateIsEquality(clauseset.head.entry.head.predicate)){
        if(!Clause.isDomainConstant(clauseset.head.entry.head.predicate.args.head.asInstanceOf[FOLFunction])){
          val func = clauseset.head.entry.head.predicate.args.head.asInstanceOf[FOLFunction]
          val interpredTupel = writeFunctionInterpredation(func,clauseset)
          result = interpredTupel._1 + interpredPredicateAndFunctionResults(interpredTupel._2)
        }
        if(!Clause.isDomainConstant(clauseset.head.entry.head.predicate.args.tail.head.asInstanceOf[FOLFunction])){
          val func = clauseset.head.entry.head.predicate.args.tail.head.asInstanceOf[FOLFunction]
          val interpredTupel = writeFunctionInterpredation(func,clauseset)
          result = interpredTupel._1 + interpredPredicateAndFunctionResults(interpredTupel._2)
        }
        if (result.equals(""))                                                                            //beide Argumente waren Domänenelemente
          result = interpredPredicateAndFunctionResults(clauseset.tail)
      }
      else{
        val pred = clauseset.head.entry.head.predicate
        val interpredTupel = writePredicateInterpretation(pred,clauseset)
        result = interpredTupel._1 + interpredPredicateAndFunctionResults(interpredTupel._2)
      }
      return result
  }

  def writePredicateInterpretation(pred:FOLPredicate,clauseset:Set[Clause]):(String,Set[Clause])={
    var returnSet = clauseset
    var returnString = "\nPredicate: "+pred.symbol.name+ "\n"
    for (c<-clauseset){
      if (c.entry.head.predicate.symbol.name.equals(pred.symbol.name)){
         returnSet = returnSet-c
         returnString = returnString + c.entry.head.predicate + " = " + c.entry.head.phase+"\n"
      }
    }
    return (returnString,returnSet)
  }

  def writeFunctionInterpredation(func:FOLFunction,clauseset:Set[Clause]):(String,Set[Clause])={
    var returnSet = clauseset
    var returnString = "\nFunction: "+func.symbol.name+ "\n"
    for (c<-clauseset){
      if (Clause.predicateIsEquality(c.entry.head.predicate)){
        if (c.entry.head.predicate.args.head.asInstanceOf[FOLFunction].symbol.name.equals(func.symbol.name)){
          returnSet = returnSet-c
          if(c.entry.head.phase)
            returnString = returnString + c.entry.head.predicate.args.head + " = " + c.entry.head.predicate.args.tail.head+"\n"
          else
            returnString = returnString + c.entry.head.predicate.args.head + " != " + c.entry.head.predicate.args.tail.head+"\n"
        }
        if (c.entry.head.predicate.args.tail.head.asInstanceOf[FOLFunction].symbol.name.equals(func.symbol.name)){
          returnSet = returnSet-c
          if(c.entry.head.phase)
            returnString = returnString + c.entry.head.predicate.args.tail.head + " = " + c.entry.head.predicate.args.head+"\n"
          else
            returnString = returnString + c.entry.head.predicate.args.tail.head + " != " + c.entry.head.predicate.args.head+"\n"
        }
      }
    }
    return (returnString,returnSet)
  }

  def run(cnf:CNF,domain:Int):Option[Set[Clause]]={
    //val flattendcnf = runflatten(cnf)
    val funcclauses = functionaldefs(domain,cnf)
    val clauseset = cnf.clauseset
    val ps = new Picosat
    var result:Option[Set[Clause]] = None
    sat(ps) {
      (solver: Solver) => {
        for(n<-funcclauses){
          solver.add(n.translateToPL())
        }
        for (c<-clauseset){
          c.clauseflatten.testClause(solver,domain)
        }
        if (solver.sat(Infinity)==1)
          result = Some(translateToModel(solver.getModel()))
      }}
    return result
  }

  def testClauseInstantiation(c:Option[Clause],solver:Solver):Boolean={
    if (!c.isEmpty)
      solver.add(c.get.translateToPL())
    return (solver.sat(Infinity)==1)
  }

  /**
   * flattens the cnf
   * @param cnf
   * @return
   */
  def runflatten(cnf: CNF): CNF ={
    getfreeVariableName(cnf)
    val newcnf = CNF(cnf.clauseset.map(c => c.clauseflatten))
    newcnf
  }

  def runBinarySplit(cnf:CNF):CNF={
    getfreePredicateName(cnf)
    var newclauseset = cnf.clauseset.foldLeft(Set[Clause]())((total:Set[Clause],clause:Clause) => clause.binarySplit() ++ total)
    return CNF(newclauseset)
  }

  def runSplitGrounds(cnf:CNF):CNF={
    getfreeConstantName(cnf)
    var newclauseset =cnf.clauseset.foldLeft(Set[Clause]())((total:Set[Clause],clause:Clause) => clause.splitGrounds() ++ total)
    return CNF(newclauseset)
  }

  def createnewVariableName(term:FOLFunction)={
    val v = FOLVariable(variableName+(varhash.size+1).toString)
    varhash.put(term,v)
  }

  def createnewConstantName(term:FOLFunction)={
    val c =FOLFunction(constantName++(constantHash.size+1).toString)
    constantHash.put(term,c)
  }

  def createnewPredicateName():String={
    predcounter=predcounter+1
    predicateName+predcounter.toString
  }

  def getfreeVariableName(cnf:CNF)={
    variableName = getfreeVariableNameHelper(cnf.getVariables.toList,cnf)
  }

 def getfreeConstantName(cnf:CNF)={
    constantName = getfreeConstantNameHelper(cnf.getFunctions,cnf)
  }

  def getfreeVariableNameHelper(vars:List[Variable[FOL]],cnf:CNF):String={
    if (vars.isEmpty)
    return variableName

    if(vars.head.toString.matches(variableName + "[0-9].*")){
      variableName = "Variable"+Random.nextString(3)
      return getfreeVariableNameHelper(cnf.getVariables.toList,cnf)
    }else{
      return getfreeVariableNameHelper(vars.tail,cnf)
    }
  }

  def getfreePredicateName(cnf:CNF)={
    predicateName = getfreePredicateNameHelper(cnf.getPredicates.toList,cnf)
  }

  def getfreePredicateNameHelper(names:List[String],cnf:CNF):String={
    if (names.isEmpty)
      return predicateName

    if(names.head.toString.matches(predicateName + "[0-9].*")){
      predicateName = "Predicate"+Random.nextString(3)
      return getfreePredicateNameHelper(cnf.getPredicates.toList,cnf)
    }else{
      return getfreePredicateNameHelper(names.tail,cnf)
    }
  }

  def getfreeConstantNameHelper(funcs:List[FunctionSymbol],cnf:CNF):String={
    if (funcs.isEmpty)
      return constantName

    if(funcs.head.name.matches(constantName + "[0-9].*")){
      constantName = "Constant" + Random.nextString(3)
      return getfreeConstantNameHelper(cnf.getFunctions,cnf)
    }else{
      return getfreeConstantNameHelper(funcs.tail,cnf)
    }
  }

  def functionaldefs(domain: Int,cnf:CNF):Set[Clause]={
    val funcs:List[FunctionSymbol]=cnf.getOnlyFunctions
    var newclauses:List[Clause]=List[Clause]()
    for(f<-funcs){
      newclauses = functionclauses(domain,f) ++ newclauses
    }
    return newclauses.toSet
  }



  def functionclauses(domain:Int,f:FunctionSymbol):List[Clause]={
    var newclauses:List[Clause]=List[Clause]()
    val funlis = allArgumentsFunctionList(domain,f)
      for (d<-1 to domain){
        for (e<-1 to domain){                                                                                           // Functional definitions
          if (d.equals(e)){
            newclauses = newclauses ++ List(Clause(Set(FOLLiteral(true,FOLPredicate("=",FOLFunction(d.toString),FOLFunction(e.toString))))))
          } else{
            for (f:FOLFunction <-funlis){
              newclauses = newclauses ++ List(Clause(Set(FOLLiteral(false,FOLPredicate("=",f,FOLFunction(d.toString()))),FOLLiteral(false,FOLPredicate("=",f,FOLFunction(e.toString()))))))
            }
            newclauses = newclauses ++ List(Clause(Set(FOLLiteral(false,FOLPredicate("=",FOLFunction(d.toString),FOLFunction(e.toString))))))
          }

        }
      }
    for (f<-funlis){
        var newfunclauseset=Set[FOLLiteral]()                                                                                   //Totality definitions
        for (i<- 1 to domain){
          newfunclauseset = newfunclauseset ++ Set(FOLLiteral(true,FOLPredicate("=",f,FOLFunction(i.toString()))))
        }
        newclauses = newclauses ++ List(Clause(newfunclauseset))
      }

    return newclauses
  }

  /**
   * builds a list of all possible arguments for the FunctionSymbol and the domain
   * @param domain
   * @param f
   * @return
   */
  def allArgumentsFunctionList(domain:Int,f:FunctionSymbol):List[FOLFunction]={
    var newFunctionslis = List[FOLFunction]()
    if(f.arity == 0)
      return List(FOLFunction(f))
    for(m<-Clause.allNTuples(f.arity,Clause.toCartesianInput((1 until domain+1).toStream))){
        newFunctionslis = newFunctionslis++ List(FOLFunction(f,m.map(i=>FOLFunction(i.toString)).toSeq:_*))
    }
    return newFunctionslis
  }

  def translateToModel(form:Formula[PL]):Set[Clause]={
    var result = Set():Set[Clause]
    form match {
      case And(preds@_*) => for(p:Formula[PL]<-preds){result= result ++ translateToModel(p)}
                            return result
      case atom:Atom[PL] => return Set(Clause(Set(FOLLiteral(true,predhashreverse.get(atom).get))))
      case Not(atom:Atom[PL]) => return Set(Clause(Set(FOLLiteral(false,predhashreverse.get(atom).get))))
      case other => sys.error("Something went wrong with the translate to Model of the sat-solver result: The entry was no And but: "+form.toString)
      }
    }

  def buildPredicates(p:FOLPredicate):FOLPredicate={
    if (Clause.predicateIsEquality(p)){
      val reversepred = new FOLPredicate(p.symbol,p.args.reverse:_*)
       if (Modelfinder.predhash.contains(reversepred)){
         return reversepred
       }
    }

    if(!Modelfinder.predhash.contains(p)){
      val c = Clause.createPlAtom
      Modelfinder.predhash.put(p,c)
      Modelfinder.predhashreverse.put(c,p)
    }
    return p
  }
}