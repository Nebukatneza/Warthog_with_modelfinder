package org.warthog.fol.semidecisionprocedures.modelfinder

import org.warthog.fol.formulas.FOLPredicate

/**
 * Created with IntelliJ IDEA.
 * User: Nebu
 * Date: 27.05.12
 * Time: 18:47
 * To change this template use File | Settings | File Templates.
 */

case class FOLLiteral(phase:Boolean,predicate:FOLPredicate) {
  override def toString:String = if(phase){
                             return predicate.toString}
                          else
                             return "!("+predicate.toString+")"
}
