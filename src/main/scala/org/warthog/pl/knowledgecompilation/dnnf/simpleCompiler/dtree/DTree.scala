package org.warthog.pl.knowledgecompilation.dnnf.simpleCompiler.dtree

import org.warthog.pl.knowledgecompilation.dnnf.Lit

/**
 * Trait for a Decomposition Tree (DTree) for the SimpleCompiler
 *
 * Author: hildebrandt
 * Date:
 */
sealed trait DTree {

  /** All variables of this DTree */
  val varSet: Set[Int]

  /** Returns the ClauseIDs in this DTree */
  def currentClauseIDs: Set[Int]

  /** Computes the separator in this DTree */
  def currentSeparator: Set[Int]

  /**
   * Counts the number of occurrences for each variable in vars
   * @param vars An array of variables whose occurrences should be counted
   * @return An array containing the number of occurrences for each variable in vars
   */
  def countOccurrences(vars: List[Int]): List[Int]
}

case class DTreeNode(lChild: DTree, rChild: DTree) extends DTree {
  lazy val varSet = lChild.varSet union rChild.varSet

  def currentClauseIDs = lChild.currentClauseIDs union rChild.currentClauseIDs

  /** The separator of a node is defined as the intersection of the variables sets of its children */
  def currentSeparator: Set[Int] = lChild.varSet intersect rChild.varSet

  def countOccurrences(vars: List[Int]) = {
    val l = lChild.countOccurrences(vars)
    val r = rChild.countOccurrences(vars)
    l zip r map (n => n._1 + n._2)
  }
}

case class DTreeLeaf(clauseID: Int, clause: Set[Lit]) extends DTree {
  lazy val varSet = clause.map(_.variable)

  def currentClauseIDs = Set(clauseID)

  /** The separator of a dtree leaf is trivially empty */
  def currentSeparator = Set()

  def countOccurrences(vars: List[Int]) = vars.map(v => if (varSet.contains(v)) 1 else 0)
}