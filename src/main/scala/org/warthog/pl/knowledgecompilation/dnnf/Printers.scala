package org.warthog.pl.knowledgecompilation.dnnf

import java.io.PrintStream
import java.util.IdentityHashMap
import collection.JavaConversions
import simpleCompiler.dtree.{DTree => STree, DTreeLeaf => SLeaf, DTreeNode => SNode}
import advancedCompiler.dtree.{DTree => ATree, DTreeLeaf => ALeaf, DTreeNode => ANode}
import de.stzoit.prover.cnf.CNFSolver


/**
 * This object contains some useful methods
 * for creating dot-files
 *
 * Author: hildebrandt
 * Date:
 */
object Dot {
  val startDigraph = "digraph {\n"
  val endGraph = "}"

  /** Returns a string representing a simple dot-node with id n and label label */
  def node(n: Long, label: String): String = n + " [label=\"" + label + "\"];"

  /** Returns a string representing a dot-node with box-shape */
  def boxNode(n: Long, label: String): String = n + " [label=\"" + label + "\",shape=box];"

  /** Returns a string representing a dot-edge */
  def edge(from: Long, to: Long): String = from + " -> " + to + ";"
}

/**
 * This object contains methods for printing dtrees (simple or advanced compiler)
 * to dot-files
 * The printStream can be changed by just setting defaultPrintStream
 * to the desired value
 *
 * Author: hildebrandt
 * Date:
 */
object DTreePrinter {

  var defaultPrintStream = System.out
  var currentID: Long = 0

  /**
   * Prints a dtree (simple compiler) to the defaultPrintStream
   * @param tree The dtree to print
   */
  def print(tree: STree) = {

    val out = defaultPrintStream

    def printTree(t: STree): Unit = {
      currentID += 1
      t match {
        case t: SLeaf => {
          out.println(
            Dot.node(currentID, "{" +
              (if (t.clause.isEmpty)
                ""
              else
                t.clause.mkString(",")
                ) + "}"))
        }
        case t: SNode => {
          val nodeID = currentID
          out.println(Dot.boxNode(nodeID, "S: " + t.currentSeparator.mkString(",")))

          /* Edge to lChild */
          out.println(Dot.edge(nodeID, currentID + 1))
          printTree(t.lChild)

          /* Edge to RChild */
          out.println(Dot.edge(nodeID, currentID + 1))
          printTree(t.rChild)
        }
      }
    }

    currentID = 0
    out.println(Dot.startDigraph)
    printTree(tree)
    out.println(Dot.endGraph)
  }

  /**
   * Prints a dtree (advanced compiler) to the defaultPrintStream
   * @param tree The dtree to print
   */
  def print(tree: ATree) = {

    val out = defaultPrintStream

    def printTree(t: ATree): Unit = {
      currentID += 1
      t match {
        case t: ALeaf => {
          out.println(
            Dot.node(currentID, t.clauseId + " {" +
              (if (t.clause.isEmpty)
                ""
              else
                t.clause.map(l => (if (CNFSolver.sign(l)) "" else "-")+CNFSolver.lit2var(l)).mkString(" ")
                ) + "}"))
        }
        case t: ANode => {
          val nodeID = currentID
          out.println(Dot.node(nodeID,""))

          /* Edge to lChild */
          out.println(Dot.edge(nodeID, currentID + 1))
          printTree(t.left)

          /* Edge to RChild */
          out.println(Dot.edge(nodeID, currentID + 1))
          printTree(t.right)
        }
      }
    }

    currentID = 0
    out.println(Dot.startDigraph)
    printTree(tree)
    out.println(Dot.endGraph)
  }
}

/**
 * This object contains a method for printing DNNFs to dot-files
 *
 * Author: hildebrandt
 * Date:
 */
object DNNFPrinter {

  var currentID = 0L
  /** Since a DNNF is a DAG and not a tree we need to remember the nodes we already visited */
  val visitedNodes = JavaConversions.mapAsScalaMap[DNNF, Long](new IdentityHashMap[DNNF, Long])

  /**
   * Prints a DNNF to out
   * @param dnnf The dtree to print
   * @param out Optional parameter for the printstream, default is System.out
   */
  def print(dnnf: DNNF, out: PrintStream = System.out) = {

    def printDNNF(t: DNNF): Unit = {
      currentID += 1
      visitedNodes += t -> currentID

      t match {
        case False => out.println(Dot.node(currentID, "False"))
        case True => out.println(Dot.node(currentID, "True"))
        case Lit(v, p) => out.println(Dot.node(currentID, (if (!p) "-" else "") + v.toString))
        case StringLit(v, p) => out.println(Dot.node(currentID, (if (!p) "-" else "") + v.toString))
        case And(args@_*) =>
          out.println(Dot.node(currentID, "And"))
          printArgs(args: _*)
        case Or(args@_*) =>
          out.println(Dot.node(currentID, "Or"))
          printArgs(args: _*)
      }
    }

    def printArgs(args: DNNF*) = {
      val nodeID = currentID
      args.foreach(c => {
        visitedNodes.get(c) match {
          case Some(n) => out.println(Dot.edge(nodeID, n))
          case None => out.println(Dot.edge(nodeID, currentID + 1)); printDNNF(c)
        }
      })
    }

    currentID = 0L
    visitedNodes.clear
    out.println(Dot.startDigraph)
    printDNNF(dnnf)
    out.println(Dot.endGraph)
  }
}