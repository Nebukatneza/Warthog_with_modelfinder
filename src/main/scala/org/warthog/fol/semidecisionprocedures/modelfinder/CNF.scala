package org.warthog.fol.semidecisionprocedures.modelfinder

import org.warthog.generic.formulas.Variable
import org.warthog.fol.formulas._
import org.warthog.fol.formulas.FunctionSymbol
import org.warthog.fol.formulas.FOLVariable
import scala.Some
import org.warthog.fol.semidecisionprocedures.modelfinder.CNF


case class CNF(clauseset: Set[Clause]){

  def getVariables:Set[Variable[FOL]]= clauseset.foldLeft(Set[Variable[FOL]]())((total:Set[Variable[FOL]],clause:Clause) => clause.getVariables ++ total)
  def getPredicates:Set[String]=clauseset.foldLeft(Set[String]())((total:Set[String],clause:Clause) => clause.getPredicates ++ total)

  def substitute(varmap:Map[FOLVariable,FOLTerm]):CNF={
              //CNF(clauseset.map(c => c.substitute(varmap)))
    var resultset = Set[Clause]()
    for (c<-clauseset){
      c.substitute(varmap) match {
        case Some(s)=>resultset = resultset ++ Set(s)
        case None =>
      }
    }
    return CNF(resultset)
  }
  def getFunctions:List[FunctionSymbol]=clauseset.foldLeft(List[FunctionSymbol]())((total:List[FunctionSymbol],clause:Clause)=> clause.getFunctions ++ total).toSet.toList

  def getOnlyFunctions:List[FunctionSymbol]={
    var resultList:List[FunctionSymbol]=List[FunctionSymbol]()
      for(f<-this.getFunctions){
        if (!(f.arity == 0 && f.name.matches("[0-9].*")))
          resultList = f::resultList
      }
    return resultList
  }

}