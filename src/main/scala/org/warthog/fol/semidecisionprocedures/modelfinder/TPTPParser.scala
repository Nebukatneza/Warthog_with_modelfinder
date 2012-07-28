package org.warthog.fol.semidecisionprocedures.modelfinder

import org.warthog.fol.parsers.tptp._
import org.warthog.fol.formulas.{FOL, FOLPredicate, FOLFormula}
import org.warthog.generic.formulas.{Not, Formula,Or}

/**
 * Created with IntelliJ IDEA.
 * User: Nebu
 * Date: 10.07.12
 * Time: 14:07
 * To change this template use File | Settings | File Templates.
 */

object TPTPParser {

  val filename = "L:/Bachelor/TPTP-v5.4.0/TPTP-v5.4.0/Axioms/GRP005-0.ax"


  def readFile(name:String):Array[String]={
    var lineList = List[String]()
    for (line<-scala.io.Source.fromFile(name).getLines){
       lineList=line::lineList
    }
    var lineArray = new Array[String](lineList.size)
    var arraycounter = lineList.size - 1
    for (l<-lineList){
      lineArray(arraycounter)=l
      arraycounter= arraycounter-1
    }

   return lineArray
  }

  def interpredProblem(name:String):CNF={
    val lineArray = readFile(name)
    var litset = Set[FOLFormula]()
    var clauseset = Set[Clause]()
    var i = 0
    while(i < lineArray.size){
      lineArray(i).toSeq match {
        case Seq('c','n','f','(',suffix@_*)=> {
          var j = 1
          var resultLiterals= suffix.toString()
          //println(suffix.toString().split(",").toSet[String].map(s=>s.fol))
          while(lineArray.isDefinedAt(i+j) && (!lineArray(i+j).equals(""))){
            resultLiterals = resultLiterals+lineArray(i+j)
            j=j+1
          }
          //litset = litset++resultLiterals
          clauseset = clauseset + cnfparse(resultLiterals)
        }
        case other =>


      }
      i=i+1
      //println(litset)
    }
        return CNF(clauseset)
  }

  def cnfparse(str:String):Clause= {
    var workstr = str
    workstr = workstr.reverse.tail.tail.tail.reverse

    workstr = killChar(workstr,',')
    workstr = killChar(workstr,',')
    workstr = killChar(workstr,'(')
    var litset = Set[FOLLiteral]()
    litset = litset ++ parseFormula(workstr.fol)
    return Clause(litset)
  }

  def killChar(str:String, char:Char):String={
    val a = str.indexOf(char)
    val outstr = str.substring(a+1)
    return outstr
  }

  def parseFormula(form :Formula[FOL]):Set[FOLLiteral]= form match{
    case Not(form:FOLPredicate) => Set(FOLLiteral(false,form))
    case y:FOLPredicate => Set(FOLLiteral(true,y))
    case Or(preds@_*) => var litset= Set[FOLLiteral]()
                        for(p<-preds)
                          litset = litset ++ parseFormula(p)
                        litset
    case other => sys.error("This should not have happend!" + other.toString)
  }

}
