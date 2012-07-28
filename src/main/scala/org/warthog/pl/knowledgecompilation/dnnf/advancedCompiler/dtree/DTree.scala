package org.warthog.pl.knowledgecompilation.dnnf.advancedCompiler.dtree

import de.stzoit.prover.cnf.CNFSolver

/**
 * Trait for a Decomposition Tree (DTree) for the AdvancedCompiler
 * This is either a DTreeNode or a DTreeLeaf
 *
 * Author: hildebrandt
 * Date:
 */
sealed trait DTree {

  /** All variables of this DTree */
  val varSet: Set[Int]

  /**
   * Computes the current variable set of this dtree
   * The current variable set includes all variables which:
   *  - are not yet assigned and
   *  - occur in clauses that are currently not subsumed
   * @param solver The CNFSolver which knows the current variable assignment
   * @return The current variable set of this dtree
   */
  def currentVarSet(solver: CNFSolver): Set[Int]

  /**
   * The current separator of this dtree
   * @param solver The CNFSolver which knows the current variable assignment
   * @return The current separator of this dtree
   */
  def currentSeparator(solver: CNFSolver): Set[Int]

  /**
   * The ids of all non-subsumed clauses in this dtree
   * @param solver The CNFSolver which knows the current variable assignment
   * @return The current clause ids
   */
  def currentClauseIds(solver: CNFSolver): Set[Int]

  /**
   * Counts the number of unsubsumed occurrences for each variable in vars
   * @param solver The CNFSolver which knows the current variable assignment
   * @param vars An array of variables whose occurrences should be counted
   * @return An array containing the number of unsubsumed occurrences for each variable in vars
   */
  def countUnsubsumedOccurrences(solver: CNFSolver, vars: Array[Int]): Array[Int]
}


/**
 * A DTreeNode with two children
 * @param left The left child which is another dtree
 * @param right The right child which is another dtree
 */
case class DTreeNode(val left: DTree, val right: DTree) extends DTree {
  lazy val varSet = left.varSet union right.varSet

  override def toString() = "Node(" + left + "," + right + ")"

  def currentVarSet(solver: CNFSolver) = left.currentVarSet(solver) union right.currentVarSet(solver)

  /** The separator of a node is defined as the intersection of the variables sets of its children */
  def currentSeparator(solver: CNFSolver) = left.currentVarSet(solver) intersect right.currentVarSet(solver)

  def currentClauseIds(solver: CNFSolver) = left.currentClauseIds(solver) union right.currentClauseIds(solver)

  def countUnsubsumedOccurrences(solver: CNFSolver, vars: Array[Int]) = {
    val l = left.countUnsubsumedOccurrences(solver, vars)
    val r = right.countUnsubsumedOccurrences(solver, vars)
    l zip r map (n => n._1 + n._2)
  }
}

/**
 * A DTreeLeaf represents a clause
 * @param clauseId An Int which uniquely identifies the clause
 * @param clause The clause represented by this DTreeLeaf
 */
case class DTreeLeaf(val clauseId: Int, val clause: Set[Int]) extends DTree {
  lazy val varSet = clause.map(_ / 2)

  override def toString() = "Leaf(" + clauseId + ",{" + clause.map(l => (if (CNFSolver.sign(l)) "" else "-")+CNFSolver.lit2var(l)).mkString(",") + "})"

  /*
   * compute current variable set of clause at dtree leaf,
   * \emptyset if clause is satisfied under the current assignment
   */
  def currentVarSet(solver: CNFSolver) = {
    def computeCurrentVarSet(cls: Set[Int], currentVS: Set[Int]): Set[Int] =
      if (cls.isEmpty)
        currentVS
      else {
        val lit = cls.head

        if (solver.lit2val(lit) == CNFSolver.Val.TRUE) {
          /* clause satisfied */
          Set.empty[Int]
        } else if (solver.lit2val(lit) == CNFSolver.Val.FALSE) {
          computeCurrentVarSet(cls.tail, currentVS)
        } else
          computeCurrentVarSet(cls.tail, currentVS + (lit / 2))
      }
    computeCurrentVarSet(clause, Set.empty[Int])
  }

  def currentClauseIds(solver: CNFSolver) = {
    if (clause.exists(x => CNFSolver.litValue(x) == solver.lit2variable(x).get_value()))
      Set.empty[Int]
    else
      Set(clauseId)
  }

  /** The separator of a dtree leaf is trivially empty */
  def currentSeparator(solver: CNFSolver) = Set.empty[Int]

  def countUnsubsumedOccurrences(solver: CNFSolver, vars: Array[Int]) =
    if (vars.exists(solver.lit2val(_) == CNFSolver.Val.TRUE))
      Array.fill(vars.size)(0)
    else
      vars.map(v => if (varSet.contains(v)) 1 else 0)
}


object DTree {

  /**
   * Computes the cardinality of all separators in a dtree
   * @param dtree The dtree
   * @return The cardinality of all separators in the dtree
   */
  def separatorCardinality(dtree: DTree): Int = dtree match {
    case DTreeLeaf(_, clause) => 0
    case DTreeNode(left, right) => left.varSet.intersect(right.varSet).size + separatorCardinality(left) + separatorCardinality(right)
  }

  /**
   * Computes the cardinality of all separators in a dtree,
   * but the cardinality of each separator is multiplied with its depth in the dtree
   * @param dtree The dtree
   * @return The result
   */
  def separatorCardinalityWeighted(dtree: DTree): Double = {
    def sepCard(dtree: DTree, level: Double): Double = dtree match {
      case DTreeLeaf(_, clause) => 0L
      case DTreeNode(left, right) => level * left.varSet.intersect(right.varSet).size + sepCard(left, level*9/10) + sepCard(right, level*9/10)
    }
    sepCard(dtree, 100)
  }
}