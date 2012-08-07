package org.warthog.fol.semidecisionprocedures.modelfinder

import org.warthog.generic.formulas.Variable
import org.warthog.fol.formulas._
import org.warthog.fol.formulas.FunctionSymbol
import org.warthog.fol.formulas.FOLVariable
import scala.Some


case class CNF(clauseset: Set[Clause]){

  /**
    * returns all Variables of the cnf
    * @return
    */
  def getVariables:Set[Variable[FOL]]= clauseset.foldLeft(Set[Variable[FOL]]())((total:Set[Variable[FOL]],clause:Clause) => clause.getVariables ++ total)

  /**
    * returns all predicateSymbols of the cnf
    * @return
    */
  def getPredicates:Set[PredicateSymbol]=clauseset.foldLeft(Set[PredicateSymbol]())((total:Set[PredicateSymbol],clause:Clause) => clause.getPredicates ++ total)

  /**
    * substitutes all Variables in the cnf with help of the varmap
    * @param varmap the map for the substitution from FOLVariable to domainElement
    * @return a cnf with domainElements
    */
  def substitute(varmap:Map[FOLVariable,FOLTerm]):CNF={
    var resultset = Set[Clause]()
    for (c<-clauseset){
      c.substitute(varmap) match {
        case Some(s)=>resultset = resultset ++ Set(s)
        case None =>
      }
    }
    return CNF(resultset)
  }

  /**
    * returns all functionSymbols of the cnf
    * @return
    */
  def getFunctions:List[FunctionSymbol]=clauseset.foldLeft(List[FunctionSymbol]())((total:List[FunctionSymbol],clause:Clause)=> clause.getFunctions ++ total).toSet.toList

  /**
    * returns all functionSymbols, which are not domainElements, of the cnf
    * @return
    */
  def getOnlyFunctions:List[FunctionSymbol]={
    var resultList:List[FunctionSymbol]=List[FunctionSymbol]()
      for(f<-this.getFunctions){
        if (!(f.arity == 0 && f.name.matches("[0-9].*")))
          resultList = f::resultList
      }
    return resultList
  }

}