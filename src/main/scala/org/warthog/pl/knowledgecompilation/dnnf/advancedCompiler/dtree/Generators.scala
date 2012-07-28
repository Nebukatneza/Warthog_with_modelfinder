package org.warthog.pl.knowledgecompilation.dnnf.advancedCompiler.dtree

import de.stzoit.prover.cnf.CNFSolver
import org.warthog.pl.knowledgecompilation.dnnf._

/**
 * Contains methods for generating DTrees (advanced compiler)
 *
 * Author: hildebrandt
 * Date:
 */
object Generators {

  /**
   * Generates a DTree using a primitive algorithm described in
   * A. Darwiche "Decomposable Negation Normal Form"
   *
   * @param clauses The list of clauses
   * @return A dtree containing the clauses in its leafs
   */
  def generateDTree(clauses: List[Set[Int]]): DTree = {
    val pi = clauses.toSet.flatten
    var sigma: List[DTree] = Nil
    var currentID = 0
    clauses.foreach(c => {
      sigma ::= DTreeLeaf(currentID, c)
      currentID += 1
    })

    pi.foreach(v => {
      val gamma: List[DTree] = sigma.filter(_.varSet.contains(v))
      sigma = compose(gamma) ++ sigma.filterNot(gamma.contains(_))
    })

    compose(sigma).head
  }

  private def compose(trees: List[DTree]): List[DTree] = trees.headOption match {
    case None => List()
    case Some(_) => List(compose2(trees))
  }

  private def compose1(trees: List[DTree]): DTree =
    trees.tail.foldRight(trees.head)(DTreeNode(_, _))

  /* This method seems to produce slightly better dtrees for the compilation process */
  private def compose2(trees: List[DTree]): DTree = trees.size match {
    case 1 => trees.head
    case _ =>
      val (a, b) = trees.splitAt(trees.size / 2)
      DTreeNode(compose2(a), compose2(b))
  }


  /**
   * Takes a dimacs-file and generates the dtree using the c2d-compiler.
   * Since c2d uses HyperGraph-Partitioning to produce the dtree
   * this dtree will let the compiler work orders of magnitude faster
   * @param dimacsFile The dimacs-File. Each clause in this file MUST be defined in just ONE line!
   * @return The dtree
   */
  def generateDTreeFromC2D(dimacsFile: String) = {
    val dTreeLines = createDTreeWithC2D(dimacsFile)
    val dimacsLines = io.Source.fromFile(dimacsFile).getLines.
      map(_.trim).map(_.replaceAll("\\s+", " ")).
      filterNot(l => l.isEmpty | l.startsWith("c") | l.startsWith("p")).
      toArray

    val dTreeTmp = new Array[DTree](dTreeLines.size)
    for (i <- 0 until dTreeLines.size)
      dTreeTmp(i) = dTreeLines(i)(0) match {
        case 'L' =>
          val n = dTreeLines(i).split(" ")(1).toInt
          DTreeLeaf(n, dimacsLines(n).split(" ").map(_.toInt).filterNot(_ == 0).map(v => CNFSolver.var2lit(math.abs(v), v > 0)).toSet)
        case 'I' =>
          val ns = dTreeLines(i).split(" ")
          DTreeNode(dTreeTmp(ns(1).toInt), dTreeTmp(ns(2).toInt))
        case _   => throw new Exception("")
      }

    dTreeTmp.last
  }
}
