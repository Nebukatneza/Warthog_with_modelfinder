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
    val P =  FOLLiteral(true,FOLPredicate("=",x,zwei))
    val K =  FOLLiteral(true,FOLPredicate("=",y,eins))
    val C = Clause(Set(L))
    val cnf = CNF(Set(Clause(Set(P)),Clause(Set(K)),Clause(Set(L))))//,Clause(Set(N)),Clause(Set(O)),Clause(Set(P)),Clause(Set(K))))

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


  def main(cnf:CNF,domain:Int,mode:String):String={
    val t0 = System.nanoTime : Double
    val result = "bla"//run(cnf,domain)
    val t1 = System.nanoTime : Double
    /*mode match{
       case "-help" => "possible Arguments are: -help,-cnf, -domain, -flattendcnf, -currentMap, -currentModel, -loopCounter, -maxPossibleLoops, -result\nThe date is given via Modelfinder.run(CNF,DOMAIN)"
       case "-cnf" => result._1.toString
       case "-domain" => result._2.toString
       case "-flattendcnf" => result._3.toString
       case "currentMap" => result._4.-(FOLVariable("0")).toString
       case "currentModel" => result._5.toString
       case "loopCounter" => result._6.toString
       case "maxPossibleLoops" => result._7.toString
       case "-result" => result._8.toString
       case "-time" => (t1-t0)/ 1000000.0 + " msecs"
       case _ => "For Help write -help as 3. Argument\nCNF: "+result._1.toString+
                                                    "\nDomain: "+result._2.toString+
                                                    "\nFlattend CNF: "+result._3.toString+
                                                    "\nAssinment of Variables: "+result._4.toString+
                                                    "\nModel: "+result._5.toString+
                                                    "\nInstantiation "+result._6.toString+" of "+result._7.toString+" possible Instantiations"+
                                                    "\nThe Result is "+result._8.toString+" with 1 for SAT and -1 for UNSAT"+
                                                    "\nElapsed time: " + (t1 - t0) / 1000000.0 + " msecs"
    } */
    return result
  }



  def run(cnf:CNF,domain:Int):String={
    //val flattendcnf = runflatten(cnf)
    val funcclauses = functionaldefs(domain,cnf)
    val clauseset = cnf.clauseset
    val ps = new Picosat
    var result = ""
    sat(ps) {
      (solver: Solver) => {
        for(n<-funcclauses){
          solver.add(n.translateToPL())
        }
        for (c<-clauseset){
          c.clauseflatten.testClause(solver,domain)
        }
        if (solver.sat(Infinity)==1)
          result = translateToModel(solver.getModel()).toString()
      }}
    if(!result.isEmpty)
      return "Sat"+result
    return "UNSAT"
  }






  /*def run(cnf:CNF,domain:Int):(CNF,Int,CNF,Map[FOLVariable,FOLFunction],Set[Clause],Int,Int,Int)={
    val ps = new Picosat
    var rv0:Int = 2
    getfreeNames(cnf)
    val flattendcnf = runflatten(cnf)
    val vars:List[FOLVariable]=flattendcnf.getVariables.map(f=>f.asInstanceOf[FOLVariable]).toList
    val mapLists:List[Map[FOLVariable,FOLFunction]]=createMapLists(domain,vars).map(f => f.toMap)
    val funcclauses = functionaldefs(domain,flattendcnf)
    var outString:String = ""
    var loopCounter = 0
    var maxPossibleLoops = mapLists.length
    var currentMap =  Map[FOLVariable,FOLFunction]()
    var currentModel = Set[Clause]()


    sat(ps) {
      (solver: Solver) => {
        for(n<-funcclauses){
          solver.add(n.translateToPL())
        }
        for(f<-mapLists ; if(rv0 != 1)){
          ps.mark()
          currentMap = f
          val newcnf = CNF(flattendcnf.substitute(f).clauseset)
          for(c<-newcnf.clauseset){
            solver.add(c.translateToPL())
          }
          rv0 = solver.sat(Infinity)
          if(rv0==1)
            currentModel = newcnf.clauseset//translateToModel(ps.getModel())
            //outString = "Clauses: " + translateToModel(ps.getModel()).toString+"\nMap: " + f.-(FOLVariable("0")).toString()
          else
            ps.undo()
          loopCounter = loopCounter + 1
        }

      }
    }

        return (cnf,domain,flattendcnf,currentMap,currentModel,loopCounter,maxPossibleLoops,rv0)

  }                  */

 /* def run(cnf:CNF,domain:Int):String={
    val flattendcnf = cnf //runflatten(cnf)
    val funcclauses = functionaldefs(domain,flattendcnf)
    val clauseset = flattendcnf.clauseset
    val ps = new Picosat
    var result:Option[Map[FOLVariable,Int]] = None
    sat(ps) {
      (solver: Solver) => {
        for(n<-funcclauses){
          solver.add(n.translateToPL())
        }
        ps.mark()
        result = testCNF(flattendcnf,Map(),domain,ps,solver)

      }}
    if(!result.isEmpty)
      return "Sat: "+result.get.toString()
    return "UNSAT"
  }

    def getFinalInstantiation(instantiation:Map[FOLVariable,Int]):Map[FOLVariable,FOLFunction]={
      instantiation.map(f=>(f._1->FOLFunction(f._2.toString)))
    }

    def getInitialInstantiation(instantiation:Map[FOLVariable,Int],freeVars:Set[FOLVariable],c:Clause):Option[Map[FOLVariable,Int]]={
      var resultmap = Map[FOLVariable,Int]()
      for (d<-c.getVariables.asInstanceOf[Set[FOLVariable]]){
        if(freeVars.contains(d)){
          if (instantiation.contains(d)){
              resultmap = resultmap.+(d->(instantiation.getOrElse(d,3)))
          }else
            resultmap = resultmap.+(d->1)
        }else
          resultmap = resultmap.+(d->instantiation.getOrElse(d,0))
      }
      return Some(resultmap.toSeq.sortBy(_._1.name).toMap)
  }

    def getNextInstantiation(instantiation:Map[FOLVariable,Int],freeVars:Set[FOLVariable],domain:Int):Option[Map[FOLVariable,Int]]={
      instantiation.toSeq.sortBy(_._1.name).toMap
      if (instantiation.isEmpty)
        return None
      val variable = instantiation.head._1
      val value = instantiation.head._2
       if(freeVars.contains(variable)&& (value < domain))
        return Some(instantiation.tail.+(variable -> (value + 1)).toSeq.sortBy(_._1.name).toMap)
       val newmap = getNextInstantiation(instantiation.tail,freeVars,domain)
      if(newmap.isEmpty)
       return newmap
      else
       return Some(newmap.get.+(variable->1).toSeq.sortBy(_._1.name).toMap)
  }
  */


  def testClauseInstantiation(c:Option[Clause],solver:Solver):Boolean={
    if (!c.isEmpty)
      solver.add(c.get.translateToPL())
    return (solver.sat(Infinity)==1)
  }

  /*def testCNF(cnf:CNF,inst:Map[FOLVariable,Int],domain:Int,ps:Picosat,solver:Solver):Option[Map[FOLVariable,Int]]={
    println(cnf)
    var freeVars = Set[FOLVariable]()
    var setVars = Set[FOLVariable]()
    var result = false
    var instantiation = inst
    var schleifenzähler = 1
    var instanzierungzähler = 1
    var instantiationclause:Option[Clause] = None
    for (c<-cnf.clauseset){
      result = false
      for (v<-c.getVariables){
        if (!(setVars.contains(v.asInstanceOf[FOLVariable])))
          freeVars = freeVars.+(v.asInstanceOf[FOLVariable])
      }
      var currentInstantiation:Option[Map[FOLVariable,Int]] = getInitialInstantiation(instantiation,freeVars,c)

      if(currentInstantiation.isEmpty){
        println("schleifenzähler: "+ (schleifenzähler-1) + "\n Instanzierungszähler: " + (instanzierungzähler-1) +"\n Model: " + translateToModel(ps.getModel())+"\n Instanzierung: " + instantiation+"\n InstanzierungsKlausel: " +instantiationclause )

        return None
      }
      while(!currentInstantiation.isEmpty && ! result){
        instantiationclause = c.substitute(getFinalInstantiation(currentInstantiation.get))
        result = testClauseInstantiation(instantiationclause,solver)
        instantiation = instantiation ++ currentInstantiation.get
        println(currentInstantiation + instantiation.toString())
        currentInstantiation = getNextInstantiation(currentInstantiation.get,freeVars,domain)
        if(! result){
          //println("und jetzt undo")
          ps.undo()
        }
        instanzierungzähler = instanzierungzähler +1
      }
      if(! result){
        println("RAUS")
        val newinst = getNextInstantiation(instantiation,c.getVariables.asInstanceOf[Set[FOLVariable]],domain)
        if(newinst.isEmpty)
          return None
        else
          return testCNF(cnf,newinst.get,domain,ps,solver)    //backtrack hier ist falsch!
      }
      setVars = setVars++freeVars
      freeVars = Set[FOLVariable]()
      schleifenzähler = schleifenzähler+1
    }
    println("schleifenzähler: "+ (schleifenzähler-1) + "\n Instanzierungszähler: " + (instanzierungzähler-1) +/*"\n Model: " + translateToModel(ps.getModel())+*/"\n Instanzierung: " + instantiation+"\n InstanzierungsKlausel: " +instantiationclause)
    return Some(instantiation)
  }*/

  /*def testCNF(cnf:CNF,inst:Map[FOLVariable,Int],domain:Int,ps:Picosat,solver:Solver):Option[Map[FOLVariable,Int]]={
    val clauseset = cnf.clauseset
    if(cnf.clauseset.isEmpty)
      return Some(Map[FOLVariable,Int]())
    return clauseset.head.testClause(clauseset.tail,Set[FOLVariable](),Map[FOLVariable,Int](),domain,ps,solver)._1
  } */

  /**
   * searches for free variable and constant names in the cnf
   * //@param cnf
   */

  /*def getfreeNames(cnf:CNF)={
  getfreeVariableName(cnf)
  //getfreeConstantName(cnf)
  } */

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

  /**
   * instantiates the variables in the cnf by values of the domain
   * @param domain
   * @param cnf
   * @return

  def instantiate(domain: Int,cnf: CNF):CNF={
    val vars:List[FOLVariable]=cnf.getVariables.map(f=>f.asInstanceOf[FOLVariable]).toList
    val mapLists:List[Map[FOLVariable,FOLFunction]/]=createMapLists(domain,vars).map(f => f.toMap)
    var newcnf=CNF(Set())
    for(f<-mapLists){
      newcnf = CNF(cnf.substitute(f).clauseset++newcnf.clauseset)
    }
    return newcnf
  }*/

  def functionaldefs(domain: Int,cnf:CNF):Set[Clause]={
    val funcs:List[FunctionSymbol]=cnf.getOnlyFunctions
    var newclauses:List[Clause]=List[Clause]()
    for(f<-funcs){
      newclauses = functionclauses(domain,f) ++ newclauses
    }
    if (funcs.isEmpty){
      for (d<-1 to domain){
        for (e<-1 to domain){                                                                                           // Functional definitions
          if (d.equals(e)){
            newclauses = newclauses ++ List(Clause(Set(FOLLiteral(true,FOLPredicate("=",FOLFunction(d.toString),FOLFunction(e.toString))))))
          } else{

            newclauses = newclauses ++ List(Clause(Set(FOLLiteral(false,FOLPredicate("=",FOLFunction(d.toString),FOLFunction(e.toString))))))
          }
        }
      }
    }
    return newclauses.toSet
  }



  def functionclauses(domain:Int,f:FunctionSymbol):List[Clause]={
    var newclauses:List[Clause]=List[Clause]()
    val funlis = argumentFunctionList(domain,f)
      for (d<-1 to domain){
        for (e<-1 to domain){                                                                                           // Functional definitions
          if (d.equals(e)){
            newclauses = newclauses ++ List(Clause(Set(FOLLiteral(true,FOLPredicate("=",FOLFunction(d.toString),FOLFunction(e.toString))))))
          } else{
            for (f:FOLFunction <-funlis){
              newclauses = newclauses ++ List(Clause(Set(FOLLiteral(false,FOLPredicate("=",f,FOLVariable(d.toString()))),FOLLiteral(false,FOLPredicate("=",f,FOLVariable(e.toString()))))))
            }
            newclauses = newclauses ++ List(Clause(Set(FOLLiteral(false,FOLPredicate("=",FOLFunction(d.toString),FOLFunction(e.toString))))))
          }

        }
        var newfunclause=Clause(Set())                                                                                   //Totality definitions
        for (f<-funlis){
          newfunclause = Clause(newfunclause.entry ++ Set(FOLLiteral(true,FOLPredicate("=",f,FOLVariable(d.toString())))))
        }
        newclauses = newclauses ++ List(newfunclause)
      }

    return newclauses
  }

  /**
   * builds a list of all possible arguments for the FunctionSymbol and the domain
   * @param domain
   * @param f
   * @return
   */
  def argumentFunctionList(domain:Int,f:FunctionSymbol):List[FOLFunction]={
     val lis:List[List[FOLVariable]] = buildArityLists(domain,f.arity)
     var newFunctionslis = List[FOLFunction]()
     for (l<-lis){
                  newFunctionslis = newFunctionslis++ List(FOLFunction(f,l.toSeq:_*))
     }
    return newFunctionslis
  }

  /**
   * builds a list of different argument for the given arity and the domain
   * @param domain
   * @param arity
   * @return
   */
  def buildArityLists(domain:Int,arity:Int):List[List[FOLVariable]]={
    if (arity==0){
      return List(List())
    }
    var newArityLists=List[List[FOLVariable]]()
    val rekurs = buildArityLists(domain,arity-1)
    for(d<-1 to domain){
       newArityLists = newArityLists ++ rekurs.map(f=>f++List(FOLVariable(d.toString)))
    }
  return newArityLists
  }

  /**
   * builds a List of all Maps from Variables to domainelements
   * //@param domain
   * //@param vars
   * //@return
   */
  /*def createMapLists(domain: Int,vars: List[FOLVariable]):List[Map[FOLVariable,FOLFunction]]={
    if (vars==List[Map[FOLVariable,FOLFunction]]())
      {return List(Map(FOLVariable("0")->FOLFunction("0")))}
    var mapList = createMapLists(domain:Int,vars.tail)
    var newList = List[Map[FOLVariable,FOLFunction]]()
    for(i<-1 to domain){
     newList = newList ++ mapList.map(m => mappinghelper(m,vars.head,FOLFunction(FunctionSymbol(i.toString(),0))))
    }
    return newList
  }  */

  def mappinghelper(m:Map[FOLVariable,FOLFunction],v:FOLVariable,i:FOLFunction) = m.+(v -> i)

  def translateToModel(form:Formula[PL]):Set[Clause]={
    var result = Set():Set[Clause]
    form match {
      case And(preds@_*) => for(p:Formula[PL]<-preds){result= result ++ Set(translateToModelHelper(p))}
                            return result
      case atom:Atom[PL] => return Set(translateToModelHelper(atom))
      case Not(atom:Atom[PL]) => return Set(translateToModelHelper(Not(atom)))
      case other => sys.error("Something went wrong with the translate to Model of the sat-solver result: The entry was no And but: "+form.toString)
      }


    }


    def translateToModelHelper(form:Formula[PL]):Clause={
      form match {
        case Not(atom:Atom[PL]) =>  Clause(Set(FOLLiteral(false,predhashreverse.get(atom).get)))
        case atom:Atom[PL] => Clause(Set(FOLLiteral(true,predhashreverse.get(atom).get)))
        case other => sys.error("Something went wrong with the translate to Model of the sat-solver result: The entry was no Atom")

      }
    }



}