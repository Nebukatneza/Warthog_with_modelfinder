package org.warthog.fol.semidecisionprocedures.modelfinder

import org.warthog.fol.formulas._
import scala.Predef._
import org.warthog.pl.parsers._
import org.warthog.pl.formulas.{PL, PLFormula, PLAtom}
import org.warthog.generic.formulas._
import collection.mutable
import collection.mutable.HashMap
import org.warthog.pl.decisionprocedures.satsolver.impl.picosat.Picosat
import org.warthog.pl.decisionprocedures.satsolver.{Infinity, Solver}


/**
 * Created with IntelliJ IDEA.
 * User: Nebukatneza
 * Date: 26.04.12
 * Time: 15:32
 * To change this template use File | Settings | File Templates.
 */

case class Clause(entry: Set[FOLLiteral]) {
  override def toString = "Clause: ["+this.entry.toString+" ] "


  /**
    * flattens the clause
    * @return
    */
  def clauseflatten:Clause ={
    var result = Set[FOLLiteral]()
    for (l<-this.entry){
      val newlitsset=Clause.predicateflatten(l)
      if(newlitsset._2.isEmpty)
        result = result ++ newlitsset._1
      else{
        val newclause = Clause(this.entry - l)
        if (newclause.entry.isEmpty)
          return this
        return newclause.varsubst(newlitsset._2.get).clauseflatten
      }
    }
    return Clause(result)
  }

  /**
    * returns the Set of Variables of the clause
    * @return
    */
  def getVariables:Set[Variable[FOL]]={
    entry.foldLeft(Set[Variable[FOL]]())((total:Set[Variable[FOL]],lit:FOLLiteral) =>lit.predicate.vars.toSet ++ total)
  }

  /**
    * returns the Set of PredicateSymbols of the clause
    * @return
    */
  def getPredicates:Set[PredicateSymbol]={
    entry.foldLeft(Set[PredicateSymbol]())((total:Set[PredicateSymbol],lit:FOLLiteral) =>total + lit.predicate.symbol)
  }


  /**
    * returns the List of FunctionSymbols of the clause
    * @return
    */
  def getFunctions:List[FunctionSymbol]=  entry.foldLeft(List[FunctionSymbol]())((total:List[FunctionSymbol],lit:FOLLiteral) =>lit.predicate.functions ++ total)


  /**
    * instantiates the Clause
    * @param varmap
    * @return
    */
  def substitute(varmap:Map[FOLVariable,FOLTerm]):Option[Clause]={
    Clause.instantiate(entry.toList,varmap) match{
      case None => None
      case Some(s)=> Some(Clause(s.toSet))
    }
  }


  /**
    * translates the Clause to a Formula[PL]
    * @return Formula[PL]
    */
  def translateToPL():Formula[PL]={
    var formula:Formula[PL]=Or[PL]()
    if(entry.isEmpty)
      formula = Falsum()
    for(e<-entry){
      val p = Modelfinder.buildPredicates(e.predicate)
      if(e.phase){
        formula=Or[PL](formula,Modelfinder.predhash.get(p).get)
      }else{
        formula=Or[PL](formula,Not[PL](Modelfinder.predhash.get(p).get))
      }
    }
    return formula
  }

  /**
    * substitutes the Variables in the Clause
    * @param map
    * @return
    */
  def varsubst(map:Map[FOLVariable,FOLVariable]):Clause={
    var newlist = List[FOLLiteral]()
    for (l<-this.entry){
      newlist = FOLLiteral(l.phase,l.predicate.tsubst(map))::newlist
    }
    return Clause(newlist.toSet)
  }

  /**
    * returns the result of the binarySplit-Algorithm of the Clause
    * @return
    */
  def binarySplit():Set[Clause]={

    val splitvar = this.getSplitVar()

    if (splitvar.isEmpty)
      return Set(this)
    else
      return this.split(splitvar.get)
  }

  /**
    * splits the clause for the splitvar Variable
    * @param splitvar
    * @return
    */

  def split(splitvar:FOLVariable):Set[Clause]={
        var litsWithVar=Set[FOLLiteral]()
        var litsWithoutVar=Set[FOLLiteral]()
    for (l<-this.entry){
      if (l.predicate.vars.contains(splitvar.asInstanceOf[Variable[FOL]]))
        litsWithVar+=l
      else
        litsWithoutVar+=l
    }
    if (litsWithVar.isEmpty || litsWithoutVar.isEmpty)
      return Set(this)
    else{
      val newpredname = Modelfinder.createnewPredicateName()
      val litsWithVarNames:Set[FOLVariable] = litsWithVar.map(l=>l.predicate.vars.asInstanceOf[List[FOLVariable]]).flatten
      val litsWithoutVarNames:Set[FOLVariable] = litsWithoutVar.map(l=>l.predicate.vars.asInstanceOf[List[FOLVariable]]).flatten
      val intersect = litsWithVarNames.intersect(litsWithoutVarNames)
      if(intersect.isEmpty)
        return Set(this)
      for (l<-litsWithoutVarNames){
        if (!litsWithVarNames.contains(l)){
          val newpred = FOLPredicate(newpredname,intersect.toSeq:_*)
          val newLit1 = FOLLiteral(true,newpred)
          val newLit2 = FOLLiteral(false,newpred)
          return Set(Clause(litsWithVar + newLit1))++Clause(litsWithoutVar + newLit2).binarySplit()
        }
        }
      return Set(this)
      }

  }

  /**
    * returns a splitVariable if one exists
    * @return
    */
  def getSplitVar():Option[FOLVariable]={
    var connections:HashMap[FOLVariable,Int]=HashMap()
    for (v<-this.getVariables){
      var connectedvars:Set[Variable[FOL]]=Set[Variable[FOL]]()
      for (l<-this.entry){
        val vars:List[Variable[FOL]] = l.predicate.vars
        if (!(vars.isEmpty)&&(vars.contains(v)))
          connectedvars = connectedvars ++ vars.toSet - v
      }
      connections.+=((v.asInstanceOf[FOLVariable],connectedvars.size))
    }
    val result = connections.toSeq.sortBy(_._2)
    //println(result)
   if(!connections.isEmpty)
      return Some(result.head._1)
    else
      return None
  }

  /**
    * returns the result of the groundSplit algorithm for this clause
    * @return
    */

  def splitGrounds():Set[Clause]={
    var constantMap = Map[FOLFunction,FOLFunction]()
      for (l<-this.entry){
        for(term<-l.predicate.args){
           if (Clause.isGround(term,true)._1){
             constantMap = constantMap ++ this.createSplitGroundMap(term.asInstanceOf[FOLFunction])
           }else{
             constantMap = constantMap ++ this.splitGroundHelper(term)
           }
        }
      }
    return createSplitGroundClause(constantMap)
  }

  /**
    * returns Clauses generated by the substitutions of the map
    * @param map
    * @return
    */
  def createSplitGroundClause(map:Map[FOLFunction,FOLFunction]):Set[Clause]={
    var newclauseset=Set[Clause]()
    for (m<-map){
       newclauseset = newclauseset + Clause(Set(FOLLiteral(true,FOLPredicate("=",m._1,m._2))))
    }
      return newclauseset + this.functionsubstitute(map)
  }

  /**
    * substitutes functions of the clause
    * @param map
    * @return
    */

  def functionsubstitute(map:Map[FOLFunction,FOLFunction]):Clause={
    var newentrys = Set[FOLLiteral]()
    for (l<-this.entry){
      var newterms = List[FOLTerm]()
      for (t<-l.predicate.args){
        newterms = Clause.termsubstitute(t,map)::newterms
      }
      newentrys = newentrys + FOLLiteral(l.phase,FOLPredicate(l.predicate.symbol,newterms.reverse.toSeq: _*))
    }
    Clause(newentrys)
  }

  /**
    * adds the term to the constantHash and returns a Map from term to constant
    * @param term
    * @return
    */
  def createSplitGroundMap(term:FOLFunction):Map[FOLFunction,FOLFunction]={
      if(!Modelfinder.constantHash.contains(term))
         Modelfinder.createnewConstantName(term)
      val c = Modelfinder.constantHash.get(term).get
    return Map(term -> c)
  }

  def  splitGroundHelper(term:FOLTerm):Map[FOLFunction,FOLFunction]={
    var constantMap = Map[FOLFunction,FOLFunction]()
          if(Clause.isGround(term,true)._2){
            val args:Set[FOLTerm] = term.asInstanceOf[FOLFunction].args.toSet
            for(t<-args){
              if (Clause.isGround(t,true)._1)
                constantMap = constantMap ++ this.createSplitGroundMap(t.asInstanceOf[FOLFunction])
              else
                constantMap = constantMap ++ this.splitGroundHelper(t)
            }
            return constantMap
          }
          else
            return constantMap

  }

  /**
    * tests all the possible Instantiations for the Clause
    * @param solver
    * @param domain
    */
  def testClause(solver:Solver,domain: Int)={
    val vars = this.getVariables
     for (m<-Clause.createSubstituteMap(vars,domain) if solver.sat(Infinity)==1){
       Modelfinder.testClauseInstantiation(this.substitute(combine(vars.toList,m)),solver)
     }
  }


  /**
    * creates a Map from FOLVariable to FOLFunction from a List of Vars and List of Intergers,
    * which stand for the domain Elements
    * @param vars
    * @param ntuple
    * @return
    */
  def combine(vars:List[Variable[FOL]],ntuple:List[Int]):Map[FOLVariable,FOLFunction]={
   (vars.asInstanceOf[List[FOLVariable]] zip ntuple.map(i=> FOLFunction(i.toString))).toMap
  }

}


object Clause{
  /**
    * substitutes a function in a term via a map from FOLFunction to FOLFunction
    * @param term
    * @param map
    * @return
    */
  def termsubstitute(term:FOLTerm,map:Map[FOLFunction,FOLFunction]):FOLTerm= term match{
    case variable:FOLVariable => return variable
    case func:FOLFunction => if(map.contains(func))
                                 return map.get(func).get
                             else
                                 return FOLFunction(func.symbol,func.args.map(f=>Clause.termsubstitute(f,map)).toSeq: _*)
    case other => sys.error("Something went wrong with the termsubstitute. The Term: "+other+" is neither Variable nor Function!")
  }

  /**
    * returns a touple, which says if the term is ground as first boolean Element,
    * or is a function which could be ground as the second Element
    * start means, if this is the first recursion of the method, use by default false!
    * @param term
    * @param start
    * @return
    */
  def isGround(term:FOLTerm,start:Boolean):(Boolean,Boolean)= term match {
    case func:FOLFunction => if((func.symbol.arity==0)&&(start))
                               return (false,false)
                             else{
                                var anyGround = false
                                var unground = true
                                for (t<-func.args){
                                  if(!Clause.isGround(t,false)._1)
                                     unground = false
                                  else anyGround = true
                                }
                              return (unground,anyGround)
                             }
    case variable:FOLVariable => return (false,false)
    case other => sys.error("Something went wrong with the check if a term is Ground. The Term: "+other+" is neither Variable nor Function!")
  }

  /**
    * flattens the predicate in the given Literal and returns a Map of FOLVariables to FOLVariables
    * @param lit
    * @return
    */
  def predicateflatten(lit: FOLLiteral): (Set[FOLLiteral],Option[Map[FOLVariable,FOLVariable]]) = {
    val isEquals = Clause.predicateIsEquality(lit.predicate)
    val lisset = termsflatten(lit.predicate.args.toList,isEquals,lit.phase)
    if (lisset._3.isEmpty){
      val newlit: FOLLiteral = FOLLiteral(lit.phase,FOLPredicate(lit.predicate.symbol, lisset._1.toSeq: _*))
      return (Set[FOLLiteral](newlit) ++ lisset._2,None)
    }else{
      return (Set[FOLLiteral](),lisset._3)
    }
  }

  /**
    * flattens the List of Terms, which are arguments of a Literal and returns a new List of Terms,
    * a Set of new Literals and a Map of FOLVariables to FOLVariables
    * @param lis
    * @param isEquals
    * @param phase
    * @return
    */
  def termsflatten(lis: List[FOLTerm],isEquals:Boolean,phase:Boolean): (List[FOLTerm], Set[FOLLiteral],Option[Map[FOLVariable,FOLVariable]]) = {
    var newlis: List[(FOLTerm, Set[FOLLiteral])]=List[(FOLTerm, Set[FOLLiteral])]()
    if (isEquals){lis match{
      case List(var1:FOLVariable,var2:FOLVariable) => if(phase)
                                                        newlis = lis.map(l => termsflattenmapper(l,true))
                                                      else
                                                        return (List[FOLTerm](),Set[FOLLiteral](),Some(Map(var2->var1)))
      case List(func1:FOLFunction,func2:FOLFunction)=> newlis = List(termsflattenmapper(lis.head,false),termsflattenmapper(lis.tail.head,true))
      case other => newlis = lis.map(l => termsflattenmapper(l,true))
      }
    }else{
      newlis = lis.map(l => termsflattenmapper(l,false))
    }

    val retlis: List[FOLTerm] = newlis.map(t => t._1)
    val retset: List[Set[FOLLiteral]] = newlis.map(t => t._2)
    return (retlis, retset.toSet.flatten,None)
  }

  /**
    * matches the term to Variables or Functions and decides how it should be flattend
    * @param term
    * @param isEquals
    * @return
    */
  def termsflattenmapper(term: FOLTerm,isEquals:Boolean): (FOLTerm, Set[FOLLiteral]) =
    (term match {
      case term: FOLVariable => (term, Set[FOLLiteral]())
      case term: FOLFunction  =>
            if(isEquals){
              val lisset = termsflatten(term.args.toList,false,false)
              val newfun: FOLFunction = FOLFunction(term.symbol, lisset._1.toSeq: _*)
              return (newfun, lisset._2)
            }

            if(!Modelfinder.varhash.contains(term))
            Modelfinder.createnewVariableName(term)
          val c = Modelfinder.varhash.get(term).get
          val lisset = termsflatten(term.args.toList,false,false)
          val newfun: FOLFunction = FOLFunction(term.symbol, lisset._1.toSeq: _*)
          val newpred: FOLPredicate = FOLPredicate("=", c, newfun)
          val set2: Set[FOLLiteral] = Set[FOLLiteral](FOLLiteral(false,newpred)) ++ lisset._2
          return(c: FOLTerm, set2)
      case other => sys.error("Something went wrong with the termsflatten rekursion, Predicateargument is neither Variable nor Funktion")
    })

  /**
    * instantiates the List of Literals via the varmap
    * @param lits
    * @param varmap
    * @return
    */

  def instantiate(lits:List[FOLLiteral],varmap:Map[FOLVariable,FOLTerm]):Option[List[FOLLiteral]]={
      val result = instantiationSubstitution(lits,varmap)
      if (result._2)
        return None
      else
        return Some(result._1)
  }

  /**
    * substitutes the Variables with the DomainElements in the Literals
    * @param lits
    * @param varmap
    * @return
    */

  def instantiationSubstitution(lits:List[FOLLiteral],varmap:Map[FOLVariable,FOLTerm]):(List[FOLLiteral],Boolean)={


        if (lits==List[FOLLiteral]())
          {return (List[FOLLiteral](),false) }

        var rekurs= instantiationSubstitution(lits.tail,varmap)

        if (rekurs._2)
        {return (List[FOLLiteral](),true)}

        val newpred = lits.head.predicate.tsubst(varmap)
        eliminateTrivialEquations(newpred,lits.head.phase,rekurs)
  }

  /**
    * eliminates the predicate, if it is an trivial equation
    * @param pred
    * @param phase
    * @param rekurs
    * @return
    */
  def eliminateTrivialEquations(pred:FOLPredicate,phase:Boolean,rekurs:(List[FOLLiteral],Boolean)):(List[FOLLiteral],Boolean)={
    if (isConstantEquation(pred)){
      val constantLeft = pred.args(0)
      val constantRight = pred.args(1)
      if(constantLeft.equals(constantRight)){
        if (phase){
          return (List[FOLLiteral](),true)
        }else{
          return (rekurs._1,false)
        }
      }else{
        if(isDomainConstant(constantLeft.asInstanceOf[FOLFunction]) && isDomainConstant(constantRight.asInstanceOf[FOLFunction])){
          if(phase){
            return (rekurs._1,false)
          }else{
            return (List[FOLLiteral](),true)
          }
        }
      }
    }
    return (List(FOLLiteral(phase,pred))++rekurs._1,false)
  }


  /**
    * creates a new PLAtom, with the name "AtomX", with X as an free identifier.
    * @return
    */
  def createPlAtom:Atom[PL]=PLAtom("Atom"+(Modelfinder.predhash.size+1).toString)

  /**
    * decides if the function is a domainElement
    * @param func
    * @return
    */
  def isDomainConstant(func:FOLFunction):Boolean={
    return func.symbol.arity==0 && func.symbol.name.matches("[0-9].*")
  }

  /**
    * decides if the function is a constant
    * @param func the function
    * @return
    */
  def isConstant(func:FOLFunction):Boolean={
    return func.symbol.arity==0
  }

  /**
    * decides if the predicate is a equation and if both arguments are constants
    * @param newpred
    * @return
    */
  private def isConstantEquation(newpred:FOLPredicate):Boolean=
    (newpred.symbol.equals(PredicateSymbol("=",2)) &&
     newpred.args.head.isInstanceOf[FOLFunction] &&
     newpred.args.tail.head.isInstanceOf[FOLFunction] &&
     isConstant(newpred.args.head.asInstanceOf[FOLFunction]) &&
     isConstant(newpred.args.tail.head.asInstanceOf[FOLFunction]))

  /**
    * decides if the FOLTerm sequence contains a Variable
    * @param args sequence of FOLTerms to search in
    * @return
    */
  def containsVariable(args:Seq[FOLTerm]):Boolean={
    if(args.isEmpty)
      return false
    if (args.head.isInstanceOf[FOLVariable])
      return true
    return containsVariable(args.tail)
  }

  /**
   * Cartesian product of streams with list entries
   *
   * @param left first operand
   * @param right second operand
   * @return stream over cartesian product of operands
   */
  def cartesian[A](left: Stream[List[A]], right: Stream[List[A]]) =
    for (leftElement <- left; rightElement <- right) yield
      leftElement ++ rightElement

  implicit def toCartesianInput[A](input: Stream[A]) = input.map(List(_))

  /**
   * Generate a stream of all n-tuples (in form of List[A] as built-in scala tuples are range restricted
   * to a size of 23) over a domain stream
   *
   * @param n length of tuple
   * @param domain over which stream of n-tuples ranges
   * @return a stream of all n-tuples over domain
   */
  def allNTuples[A](n: Int, domain: Stream[List[A]]): Stream[List[A]] =
    if (n <= 1)
      domain
    else
      cartesian(domain, allNTuples[A](n-1, domain))

  /**
    * creates a Map
    * @param vars the Variables, which are about to be substituted
    * @param domain over which stream of n-tuples ranges
    * @return a stream of all Tuples over the domain and the Variables
   */
  def createSubstituteMap(vars:Set[Variable[FOL]],domain:Int):Stream[List[Int]]={
    return Clause.allNTuples(vars.size,toCartesianInput((1 until domain+1).toStream))
  }

  /**
    * checks if the predicate is the equaltity
    * @param pred the predicate to check
    * @return
    */
  def predicateIsEquality(pred:FOLPredicate):Boolean=pred.symbol.name.equals("=") && (pred.symbol.arity == 2)
}
