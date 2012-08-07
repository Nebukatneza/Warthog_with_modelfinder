package org.warthog.fol.semidecisionprocedures.modelfinder


import scala.annotation.tailrec
/**
 * Created with IntelliJ IDEA.
 * User: Nebu
 * Date: 06.08.12
 * Time: 17:04
 * To change this template use File | Settings | File Templates.
 */

object Benchmark {

  def bench(prob:Int,domain:Int,option:String):List[String]={
      var times = List[String]()
      val probs = go()
    for(i<- 1 until domain+1){


       times = getMedian(prob,i,option,probs)::times
    }
    return times.reverse
  }

  def runfinder(p:Int,domain:Int,option:String,probs:Array[String]):String={
    Modelfinder.main(TPTPProblemFileParser.interpredProblem(TPTPProblemFileParser.filehome+probs{p}),domain,option,true)
  }

  def getMedian(p:Int,domain:Int,option:String,probs:Array[String]):String={
    var times = List[Double]()
    for (i<- 1 until 5)
      times = runfinder(p,domain,option,probs).toDouble::times

    return median(times)
  }

  def median(lis:List[Double]):String={
    (lis.sortWith(_ > _)(lis.length/2)).toString
  }



  def go():Array[String]={
    val probs = new Array[String](21)
    probs{0}=("Axioms/HWV002-1.ax")

    probs{1}=("Axioms/HWV001-1.ax")

    probs{2}=("Axioms/HWV001-0.ax")

    probs{3}=("Axioms/HWV002-0.ax")

    probs{4}=("Axioms/GRP005-0.ax")

    probs{5}=("Axioms/TOP001-0.ax")

    probs{6}=("Problems/TOP/TOP003-2.p")

    probs{7}=("Problems/SYN/SYN036-2.p")

    probs{8}=("Problems/SYN/SYN084-1.p")

    probs{9}=("Problems/SWV/SWV013-1.p")

    probs{10}=("Problems/SWV/SWV012-1.p")

    probs{11}=("Axioms/PLA001-0.ax")

    probs{12}=("Problems/NLP/NLP134-1.p")

    probs{13}=("Problems/NLP/NLP031-1.p")

    probs{14}=("Problems/NLP/NLP029-1.p")

    probs{15}=("Problems/NLP/NLP028-1.p")

    probs{16}=("Problems/NLP/NLP027-1.p")

    probs{17}=("Problems/MSC/MSC009-1.p")

    probs{18}=("Problems/KRS/KRS007-1.p")

    probs{19}=("Problems/KRS/KRS006-1.p")

    probs{20}=("Problems/KRS/KRS005-1.p")

    return probs
  }

  def clauseSort()={
    val probs = go()
    var map = Map[String,Int]()
    for(p<-probs){
      map = map.+(p->clause(p))
    }
    val lis = map.toList.sortWith((e1:Tuple2[String,Int],e2:Tuple2[String,Int]) => e1._2 < e2._2)

    lis foreach println
  }

  def clauseLitSort()={
    val probs = go()
    var map = Map[String,Double]()
    for(p<-probs){
      map = map.+(p->clauseLit(p))
    }
    val lis = map.toList.sortWith((e1:Tuple2[String,Double],e2:Tuple2[String,Double]) => e1._2 < e2._2)

    lis foreach println
  }

  def varSort()={
    val probs = go()
    var map = Map[String,Int]()
    for(p<-probs){
      map = map.+(p->vars(p))
    }
    val lis = map.toList.sortWith((e1:Tuple2[String,Int],e2:Tuple2[String,Int]) => e1._2 < e2._2)

    lis foreach println
  }

  def flattenVarSort()={
    val probs = go()
    var map = Map[String,Int]()
    for(p<-probs){
      map = map.+(p->flattenVars(p))
    }
    val lis = map.toList.sortWith((e1:Tuple2[String,Int],e2:Tuple2[String,Int]) => e1._2 < e2._2)

    lis foreach println
  }

  def clause(prob:String):Int={
    TPTPProblemFileParser.interpredProblem(TPTPProblemFileParser.filehome+prob).clauseset.size
  }

  def clauseLit(prob:String):Double={
    val cs = TPTPProblemFileParser.interpredProblem(TPTPProblemFileParser.filehome+prob).clauseset
    var lits = 0.0
    for (c<-cs){
      lits = lits + c.entry.size
    }
    return  lits / cs.size
  }

  def vars(prob:String):Int={
    TPTPProblemFileParser.interpredProblem(TPTPProblemFileParser.filehome+prob).getVariables.size
  }

  def flattenVars(prob:String):Int={
    CNF(TPTPProblemFileParser.interpredProblem(TPTPProblemFileParser.filehome+prob).clauseset.map(c=>c.clauseflatten)).getVariables.size
  }




}
