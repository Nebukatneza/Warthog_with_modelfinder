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

  def getPredicates:Set[String]={
    entry.foldLeft(Set[String]())((total:Set[String],lit:FOLLiteral) =>total + lit.predicate.symbol.name)
  }


  /**
   * returns the List of FunctionSymbols of the clause
   * @return
   */
  def getFunctions:List[FunctionSymbol]=  entry.foldLeft(List[FunctionSymbol]())((total:List[FunctionSymbol],lit:FOLLiteral) =>lit.predicate.functions ++ total)

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
      if(Modelfinder.predhash.contains(e.predicate)){
        if(e.phase){
          formula=Or[PL](formula,Modelfinder.predhash.get(e.predicate).get)
        }else{
          formula=Or[PL](formula,Not[PL](Modelfinder.predhash.get(e.predicate).get))
        }

      }else{
        val c = Clause.createPlAtom
        Modelfinder.predhash.put(e.predicate,c)
        Modelfinder.predhashreverse.put(c, e.predicate)
        if(e.phase){
          formula=Or[PL](formula,Modelfinder.predhash.get(e.predicate).get)
        }else{
          formula=Or[PL](formula,Not[PL](Modelfinder.predhash.get(e.predicate).get))
        }
      }
    }
    return formula
  }

  def varsubst(map:Map[FOLVariable,FOLVariable]):Clause={
    var newlist = List[FOLLiteral]()
    for (l<-this.entry){
      newlist = FOLLiteral(l.phase,l.predicate.tsubst(map))::newlist
    }
    return Clause(newlist.toSet)
  }

  def binarySplit():Set[Clause]={

    val splitvar = this.getSplitVar()

    if (splitvar.isEmpty)
      return Set(this)
    else
      return this.split(splitvar.get)
  }

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
      //println(litsWithVarNames+"\n"+litsWithoutVarNames+"\n"+intersect)
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

  def createSplitGroundClause(map:Map[FOLFunction,FOLFunction]):Set[Clause]={
    var newclauseset=Set[Clause]()
    for (m<-map){
       newclauseset = newclauseset + Clause(Set(FOLLiteral(true,FOLPredicate("=",m._1,m._2))))
    }
      return newclauseset + this.functionsubstitute(map)
  }

  def functionsubstitute(map:Map[FOLFunction,FOLFunction]):Clause={
    var newentrys = Set[FOLLiteral]()
    for (l<-this.entry){
      var newterms = Set[FOLTerm]()
      for (t<-l.predicate.args){
        newterms = newterms + Clause.termsubstitute(t,map)
      }
      newentrys = newentrys + FOLLiteral(l.phase,FOLPredicate(l.predicate.symbol,newterms.toSeq: _*))
    }
    Clause(newentrys)
  }

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

  def testClause(solver:Solver,domain: Int)={
    val vars = this.getVariables
     for (m<-Clause.createSubstituteMap(vars,domain) if solver.sat(Infinity)<1){
       Modelfinder.testClauseInstantiation(this.substitute(combine(vars.toList,m)),solver)
     }
  }



  def combine(vars:List[Variable[FOL]],ntuple:List[Int]):Map[FOLVariable,FOLFunction]={
   (vars.asInstanceOf[List[FOLVariable]] zip ntuple.map(i=> FOLFunction(i.toString))).toMap
  }

 /* def testClause(clauseset:Set[Clause],setVars:Set[FOLVariable],inst:Map[FOLVariable,Int],domain:Int,ps:Picosat,solver:Solver):(Option[Map[FOLVariable,Int]],Boolean)={
    var result = false
    var freeVars = Set[FOLVariable]()
    var instantiation = inst
      for (v<-this.getVariables){
        if (!(setVars.contains(v.asInstanceOf[FOLVariable])))
          freeVars = freeVars.+(v.asInstanceOf[FOLVariable])
      }
      var currentInstantiation:Option[Map[FOLVariable,Int]] = Modelfinder.getInitialInstantiation(instantiation,freeVars,this)

      if(currentInstantiation.isEmpty){
        //println("schleifenzähler: "+ (schleifenzähler-1) + "\n Instanzierungszähler: " + (instanzierungzähler-1) +"\n Model: " + translateToModel(ps.getModel())+"\n Instanzierung: " + instantiation+"\n InstanzierungsKlausel: " +instantiationclause )
        println("Hier sollte man nicht rausfliegen!")
        return (None,false)
      }
      while(!currentInstantiation.isEmpty && ! result){
        val instantiationclause = this.substitute(Modelfinder.getFinalInstantiation(currentInstantiation.get))
        result = Modelfinder.testClauseInstantiation(instantiationclause,solver)
        instantiation = instantiation ++ currentInstantiation.get
        println("teste: "+instantiation.toString + " für "+this)
        currentInstantiation = Modelfinder.getNextInstantiation(currentInstantiation.get,freeVars,domain)
        if(! result){
          //println("und jetzt undo")
          ps.undo()
        }
        //instanzierungzähler = instanzierungzähler +1
      }
      if(! result){
        println("Alle Möglichkeiten durchlaufen")
        val newinst = Modelfinder.getNextInstantiation(instantiation,this.getVariables.asInstanceOf[Set[FOLVariable]],domain)
        if(newinst.isEmpty){
          println("Abbruch, gibt keine Möglichkeiten mehr")
          return (None,false)
        }
        else{
          println("Backtrack mit: "+instantiation)
          return (Some(instantiation),true)}
      }else{
        if(clauseset.isEmpty){
          println("Das war die letzte Klause! Ergebnis ist: "+ instantiation)
          return (Some(instantiation),false)
        }
        println("zur nächsten Klausel: "+ clauseset.head)
        val recurse = clauseset.head.testClause(clauseset.tail,setVars++freeVars,instantiation,domain,ps,solver)
        val backtrack = recurse._2
        if (backtrack){
          val newinst = Modelfinder.getNextInstantiation(recurse._1.get,this.getVariables.asInstanceOf[Set[FOLVariable]],domain)
          if(newinst.isEmpty){
            println("Abbruch, gibt nach Backtrack keine Möglichkeiten mehr")
            return (None,false)
          }
          return this.testClause(clauseset,setVars,newinst.get,domain,ps,solver)
        }
        return (recurse._1,false)
      }


  }     */


}


object Clause{

  def termsubstitute(term:FOLTerm,map:Map[FOLFunction,FOLFunction]):FOLTerm= term match{
    case variable:FOLVariable => return variable
    case func:FOLFunction => if(map.contains(func))
                                 return map.get(func).get
                             else
                                 return FOLFunction(func.symbol,func.args.map(f=>Clause.termsubstitute(f,map)).toSeq: _*)
    case other => sys.error("Something went wrong with the termsubstitute. The Term: "+other+" is neither Variable nor Function!")
  }

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


  def predicateflatten(lit: FOLLiteral): (Set[FOLLiteral],Option[Map[FOLVariable,FOLVariable]]) = {
    val isEquals = (lit.predicate.symbol.name.equals("=") && (lit.predicate.symbol.arity == 2))
    val lisset = termsflatten(lit.predicate.args.toList,isEquals,lit.phase)
    if (lisset._3.isEmpty){
      val newlit: FOLLiteral = FOLLiteral(lit.phase,FOLPredicate(lit.predicate.symbol, lisset._1.toSeq: _*))
      return (Set[FOLLiteral](newlit) ++ lisset._2,None)
    }else{
      return (Set[FOLLiteral](),lisset._3)
    }
  }

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

  def termsflattenmapper(term: FOLTerm,isEquals:Boolean): (FOLTerm, Set[FOLLiteral]) =
    (term match {
      case term: FOLVariable => (term, Set[FOLLiteral]())
      case term: FOLFunction  =>
            if(term.symbol.arity == 0 && term.symbol.name.matches("[0-9].*"))
              return (term, Set[FOLLiteral]())
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

  def instantiate(lits:List[FOLLiteral],varmap:Map[FOLVariable,FOLTerm]):Option[List[FOLLiteral]]={
      val result = instanciateHelper(lits,varmap)
      if (result._2)
        return None
      else
        return Some(result._1)
    /*var newlist = List[FOLLiteral]()
    for (l<-lits){
      newlist = FOLLiteral(l.phase,l.predicate.tsubst(varmap))::newlist
    }
    return newlist*/
  }

  def instanciateHelper(lits:List[FOLLiteral],varmap:Map[FOLVariable,FOLTerm]):(List[FOLLiteral],Boolean)={


        if (lits==List[FOLLiteral]())
          {return (List[FOLLiteral](),false) }

        var rekurs= instanciateHelper(lits.tail,varmap)

        if (rekurs._2)
        {return (List[FOLLiteral](),true)}

        val newpred = lits.head.predicate.tsubst(varmap)//TODO: Modularisieren
        if (isConstantEquation(newpred)){
           val constantLeft = newpred.args(0)
           val constantRight = newpred.args(1)
            if(constantLeft.equals(constantRight)){
              if (lits.head.phase){
                return (List[FOLLiteral](),true)
              }else{
                return (rekurs._1,false)
              }
            }else{
             if(isConstant(constantLeft.asInstanceOf[FOLFunction]) && isConstant(constantRight.asInstanceOf[FOLFunction])){//TODO: hier noch abfrage auf mindestens eine nichtDomänenkonstante einfügen
              if(lits.head.phase){
                return (rekurs._1,false)
              }else{
                return (List[FOLLiteral](),true)
                }
              }
            }
          }
        return (List(FOLLiteral(lits.head.phase,newpred))++rekurs._1,false)

  }



  def createPlAtom:Atom[PL]=PLAtom("Atom"+(Modelfinder.predhash.size+1).toString)

  def isConstant(func:FOLFunction):Boolean={
    return func.symbol.arity==0 && func.symbol.name.matches("[0-9].*")
  }

  private def isConstantEquation(newpred:FOLPredicate):Boolean=
    (newpred.symbol.equals(PredicateSymbol("=",2)) &&
     newpred.args.head.isInstanceOf[FOLFunction] &&
     newpred.args.tail.head.isInstanceOf[FOLFunction] &&
     isConstant(newpred.args.head.asInstanceOf[FOLFunction]) &&
     isConstant(newpred.args.tail.head.asInstanceOf[FOLFunction]))

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
   * returns stream over cartesian product of operands
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
   * returns a stream of all n-tuples over domain
   */
  def allNTuples[A](n: Int, domain: Stream[List[A]]): Stream[List[A]] =
    if (n <= 1)
      domain
    else
      cartesian(domain, allNTuples[A](n-1, domain))

  def createSubstituteMap(vars:Set[Variable[FOL]],domain:Int):Stream[List[Int]]={
    return Clause.allNTuples(vars.size,toCartesianInput((1 until domain+1).toStream))
  }
}
