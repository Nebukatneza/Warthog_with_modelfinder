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

  /**
    * Resets the Modelfinder object
    */
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
    * Runs the Modelfinder (main method) without options
    * @param cnf
    * @param domain
    * @return
    */

  def main(cnf:CNF,domain:Int):String={
    val t0 = System.nanoTime : Double
    val result = run(cnf,domain,"")
    val t1 = System.nanoTime : Double
    val viewableResult = interpredResult(result)
    return ((t1-t0)/1000000).toString+"ms\n"+ viewableResult
  }

  /**
    * Runs the Modelfinder (main method) with options (for benchmarking)
    * @param cnf
    * @param domain
    * @param option
    * @param time
    * @return
    */

  def main(cnf:CNF,domain:Int,option:String,time:Boolean):String={
    if (time)
      return getTime(cnf,domain,option)._1.toString
    else{
      val result = getTime(cnf,domain,option)
      return result._1.toString+"ms\n"+result._2.toString
    }
  }

  /**
    * Computes the time needed for the algorithm and returns a Tuple of time in ms and the result as String
    * @param cnf
    * @param domain
    * @param option
    * @return
    */

  def getTime(cnf:CNF,domain:Int,option:String):(Double,String)={
    val t0 = System.nanoTime : Double
    val result = run(cnf,domain,option)
    val t1 = System.nanoTime : Double
    return (((t1-t0)/1000000),interpredResult(result))
  }

  /**
    * gets an option for a Clauseset and interpreds it to a Stringoutput of eiter "UNSAT" or the interpreted result
    * @param maybeclauseset
    * @return
    */

  def interpredResult(maybeclauseset:Option[Set[Clause]]):String={
      if(maybeclauseset.isEmpty)
        return "UNSAT"
      val result = interpredPredicateAndFunctionResults(maybeclauseset.get)
    return result
  }


  /**
    * returns a String, which contains interpretationformulas for the Clauseset.
    * Predicates and Functions, which are added by the Algorithm are removed
    * @param clauseset
    * @return
    */
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

  /**
    * returns the interpretation for a specific predicate in the Clauseset
    * @param pred
    * @param clauseset
    * @return
    */

  def writePredicateInterpretation(pred:FOLPredicate,clauseset:Set[Clause]):(String,Set[Clause])={
    var returnSet = clauseset
    var returnString = ""
    if(!pred.symbol.name.matches(predicateName+"[0-9].*"))
      returnString = "\nPredicate: "+pred.symbol.name+ "\n"
    for (c<-clauseset){
      if (c.entry.head.predicate.symbol.name.equals(pred.symbol.name)){
         returnSet = returnSet-c
        if(!pred.symbol.name.matches(predicateName+"[0-9].*"))
         returnString = returnString + c.entry.head.predicate + " = " + c.entry.head.phase+"\n"
      }
    }
    return (returnString,returnSet)
  }


  /**
    * returns the interpretation for a specific function in the Clauseset
    * @param func
    * @param clauseset
    * @return
    */
  def writeFunctionInterpredation(func:FOLFunction,clauseset:Set[Clause]):(String,Set[Clause])={
    var returnSet = clauseset
    var returnString = ""
    if(!func.symbol.name.matches(constantName+"[0-9].*")){
      returnString = "\nFunction: "+func.symbol.name+ "\n"
    }
    for (c<-clauseset){
      if (Clause.predicateIsEquality(c.entry.head.predicate)){
        if (c.entry.head.predicate.args.head.asInstanceOf[FOLFunction].symbol.name.equals(func.symbol.name)){
          returnSet = returnSet-c
          if(!func.symbol.name.matches(constantName+"[0-9].*")){
            if(c.entry.head.phase)
              returnString = returnString + c.entry.head.predicate.args.head + " = " + c.entry.head.predicate.args.tail.head+"\n"
            else
              returnString = returnString + c.entry.head.predicate.args.head + " != " + c.entry.head.predicate.args.tail.head+"\n"
          }
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


  /**
   * runs the modelfinding Algorithm, with option to binarySplitting and groundSplitting
   * "-none" means no improvments
   * "-binSplit" means only binarySplitting as improvement
   * "-groundSplit" means only groundSplitting as improvement
   * any other options means both improvements are used
   * @param cnf
   * @param domain
   * @param option
   * @return
   */
  def run(cnf:CNF,domain:Int,option:String):Option[Set[Clause]]={
    var binSplit = true
    var groundSplit = true
    option match {
      case "-none" => {binSplit = false
                       groundSplit = false}
      case "-binSplit" => groundSplit = false
      case "-groundSplit" => binSplit = false
      case other =>
    }

    reset()
    val funcclauses = functionaldefs(domain,cnf)
    val clauseset = cnf.clauseset
    Modelfinder.getfreeVariableName(cnf)
    val ps = new Picosat
    var result:Option[Set[Clause]] = None
    sat(ps) {
      (solver: Solver) => {
        for(n<-funcclauses){
          solver.add(n.translateToPL())
        }
        for (c<-clauseset){
          if (!(binSplit||groundSplit))
            c.clauseflatten.testClause(solver,domain)
          else{
            if (!binSplit){
              for (d<-c.splitGrounds())
                d.clauseflatten.testClause(solver,domain)
            }else{
              if (!groundSplit){
                for (d<-c.clauseflatten.binarySplit)
                  d.testClause(solver,domain)
              }else{
                for (d<-c.splitGrounds())
                  for (e<-d.clauseflatten.binarySplit()){
                    e.testClause(solver,domain)
                  }
              }
            }
          }

        }
        if (solver.sat(Infinity)==1)
          result = Some(translateToModel(solver.getModel()))
      }}
    return result
  }

  /**
   * adds a specific instatiated Clause to the Solver
   * @param c
   * @param solver
   * @return
   */
  def testClauseInstantiation(c:Option[Clause],solver:Solver):Boolean={
    if (!c.isEmpty)
      solver.add(c.get.translateToPL())
    return (solver.sat(Infinity)==1)
  }

  /**
    * adds a new variable to the varhash
    * @param term
    * @return
    */
  def createnewVariableName(term:FOLFunction)={
    val v = FOLVariable(variableName+(varhash.size+1).toString)
    varhash.put(term,v)
  }


  /**
    * adds a new constant to the constantHash
    * @param term
    * @return
    */
  def createnewConstantName(term:FOLFunction)={
    val c =FOLFunction(constantName++(constantHash.size+1).toString)
    constantHash.put(term,c)
  }


  /**
    * returns a new predicatename
    * @return
    */
  def createnewPredicateName():String={
    predcounter=predcounter+1
    predicateName+predcounter.toString
  }


  /**
    * sets the variableName to a name not existing in the cnf
    * @param cnf
    */
  def getfreeVariableName(cnf:CNF)={
    variableName = getfreeVariableNameHelper(cnf.getVariables.toList,cnf)
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

  /**
    * sets the predicateName to a name not existing in the cnf
    * @param cnf
    */

  def getfreePredicateName(cnf:CNF)={
    predicateName = getfreePredicateNameHelper(cnf.getPredicates.toList,cnf)
  }

  def getfreePredicateNameHelper(symbols:List[PredicateSymbol],cnf:CNF):String={
    if (symbols.isEmpty)
      return predicateName

    if(symbols.head.name.toString.matches(predicateName + "[0-9].*")){
      predicateName = "Predicate"+Random.nextString(3)
      return getfreePredicateNameHelper(cnf.getPredicates.toList,cnf)
    }else{
      return getfreePredicateNameHelper(symbols.tail,cnf)
    }
  }

  /**
    * sets the constantName to a name not existing in the cnf
    * @param cnf
    */

  def getfreeConstantName(cnf:CNF)={
    constantName = getfreeConstantNameHelper(cnf.getFunctions,cnf)
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


  /**
    * creates the clauses for the functional dependencies of all functions in the cnf
    * @param domain
    * @param cnf
    * @return
    */
  def functionaldefs(domain: Int,cnf:CNF):Set[Clause]={
    val funcs:List[FunctionSymbol]=cnf.getOnlyFunctions
    var newclauses:List[Clause]=List[Clause]()
    for(f<-funcs){
      newclauses = functionclauses(domain,f) ++ newclauses
    }
    return newclauses.toSet
  }


  /**
    * creates the clauses for the functional dependecies for the function symbol f
    * @param domain
    * @param f
    * @return
    */
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
    for (func<-funlis){
        var newfunclauseset=Set[FOLLiteral]()                                                                                   //Totality definitions
        for (i<- 1 to domain){
          newfunclauseset = newfunclauseset ++ Set(FOLLiteral(true,FOLPredicate("=",func,FOLFunction(i.toString()))))
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

  /**
    * translates a PL Formula to a set of first order clauses
    * @param form
    * @return
    */

  def translateToModel(form:Formula[PL]):Set[Clause]={
    var result = Set():Set[Clause]
    form match {
      case And(preds@_*) => for(p:Formula[PL]<-preds){result= result ++ translateToModel(p)}
                            return result
      case atom:Atom[PL] => return Set(Clause(Set(FOLLiteral(true,predhashreverse.get(atom).get))))
      case Not(atom:Atom[PL]) => return Set(Clause(Set(FOLLiteral(false,predhashreverse.get(atom).get))))
      case _:TruthValue[PL] => return result
      case other => sys.error("Something went wrong with the translate to Model of the sat-solver result: The entry was no And but: "+form.toString)
      }
    }

  /**
    * identifies symetric equalities and adds the predicate to the predhash and predhashreverse if necessary
    * @param p
    * @return
    */

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