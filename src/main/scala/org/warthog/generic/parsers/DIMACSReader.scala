package org.warthog.generic.parsers

import org.warthog.generic.formulas._
import org.warthog.pl.formulas.{PLAtom, PL}
import org.warthog.pl.datastructures.cnf.{PLLiteral, ImmutablePLClause}
import org.warthog.fol.formulas._
import org.warthog.fol.datastructures.cnf.{FOLLiteral, ImmutableFOLClause}
import org.warthog.fol.formulas.FOLVariable
import scala.Some
import org.warthog.pl.formulas.PLAtom

/**
 * A Reader for dimacs- and qdimacs-files
 * There are methods for reading a (q)dimacs-file and returning:
 * - a List[Set[Int]]
 * - a Formula[PL]
 * - a List[ImmutablePLClause]
 *
 * - a Formula[FOL]
 * - a (List[(String, Set[Int])], List[ImmutableFOLClause])
 *
 * Author: hildebrandt
 * Date:
 */
object DIMACSReader {

  /**
   * Reads a dimacs-file and returns a corresponding Formula[PL]
   *
   * @param path The path to the dimacs-file
   * @return A corresponding Formula[PL]
   */
  def dimacs2Formula(path: String): Formula[PL] =
    And(dimacs2Clauses(path).map(
      cls => Or(cls.toList.map(lit =>
        if (lit < 0) Not(PLAtom(math.abs(lit).toString)) else PLAtom(lit.toString)): _*
      )): _*)

  /**
   * Reads a dimacs-file and returns a corresponding List of ImmutablePLClauses
   *
   * @param path The path to the dimacs-file
   * @return A corresponding List[ImmutablePLClause]
   */
  def dimacs2PLClauses(path: String): List[ImmutablePLClause] =
    dimacs2Clauses(path).map(cls =>
      new ImmutablePLClause(cls.toList.map(lit =>
        PLLiteral(math.abs(lit).toString, lit > 0)
      )))

  /**
   * Reads a dimacs-file and returns the formula
   * as list of clauses (represented as sets of ints)
   * Throws an exception if the file is actually a qdimacs-file
   *
   * @param path The path to the dimacs-file
   * @return A corresponding list of clauses (list of set of int)
   */
  def dimacs2Clauses(path: String): List[Set[Int]] = parseDimacs(path) match {
    case (None, result) => result
    case (_, _) => throw new Exception("Expected dimacs-file, found Qdimacs-file!")
  }

  /**
   * Reads a qdimacs-file and returns a corresponding Formula[FOL]
   *
   * @param path The path to the qdimacs-file
   * @return A corresponding Formula[FOL]
   */
  def qdimacs2Formula(path: String): Formula[FOL] = parseDimacs(path) match {
    case (None, _) => throw new Exception("How should we handle that?")
    case (Some(quants), clauses) =>
      val matrix = And(clauses.map(cls => Or(cls.toList.map(lit =>
        if (lit > 0) FOLPredicate(math.abs(lit).toString) else -FOLPredicate(math.abs(lit).toString)):_*)):_*)
      quants.foldRight(matrix.asInstanceOf[Formula[FOL]])((quant, formula) => quant._1 match {
        case Formula.EXISTS => FOLExists(quant._2.map(v => FOLVariable(v.toString)), formula)
        case Formula.FORALL => FOLForAll(quant._2.map(v => FOLVariable(v.toString)), formula)
        })
  }

  /**
   * Reads a qdimacs-file and returns a tupel:
   *  - The first element contains a list of tupels representing the quantifications as described in parseDimacs-method
   *  - The second element contains the list of clauses
   *
   * @param path The path to the qdimacs-file
   * @return The result
   */
  def qdimacs2FOLClauses(path: String): (List[(String, Set[Int])], List[ImmutableFOLClause]) = parseDimacs(path) match {
    case (None, _) => throw new Exception("How should we handle that?")
    case (Some(quants), clauses) =>
      val folClauses = clauses.map(cls => new ImmutableFOLClause(cls.toList.map(lit =>
        FOLLiteral(FOLPredicate(math.abs(lit).toString), lit > 0))))
      (quants, folClauses)
  }

  /**
   * Reads a dimacs- or qdimacs-file and returns
   *  - case dimacs: a tupel (None, the formula as list of clauses (represented as sets of ints))
   *  - case qdimacs: a tupel:
   *        + the first element contains a list of tupels representing the quantifications
   *              (a String which is either Formula.EXISTS or Formula.FORALL, and a list of Ints for the quantified variables)
   *        + the second element contains the list of clauses (as sets of ints)
   *
   *  If the file contains more than one preamble,
   * or the actual number of clauses/variables doesn't
   * correspond to the preamble, a message will be printed
   * to StdErr and the result be returned (ignoring the preamble)
   *
   * @param path The path to the dimacs-file
   * @return The result
   */
  private def parseDimacs(path: String): (Option[List[(String, Set[Int])]], List[Set[Int]]) = {

    var preambleRead = false
    var numberOfClausesInPreamble = 0
    var numberOfVarsInPreamble = 0
    var clauseCounter = 0
    var varCounter = Set[Int]()

    val lines = io.Source.fromFile(path).getLines()
    var lineNumber = 0

    var quantifiers = List[(String, Set[Int])]()

    var clauses = List[Set[Int]]()
    var currentClause = Set[Int]()

    while (lines.hasNext) {
      lineNumber += 1
      val line = lines.next().trim.replaceAll("\\s+", " ")

      if (!line.isEmpty) {
        line(0) match {
          case 'c' => ()
          case 'p' =>
            if (preambleRead)
              System.err.println("Line " + lineNumber + ": More than one preamble --> Use the first")
            else {
              preambleRead = true
              val tokens = line.split(" ")
              if (tokens.size == 4) {
                try {
                  numberOfVarsInPreamble = tokens(2).toInt
                  numberOfClausesInPreamble = tokens(3).toInt
                }
                catch {
                  case e: NumberFormatException => System.err.println("Line " + lineNumber + ": Number format exception in preamble --> Skip line")
                }
              }
              else
                System.err.println("Line " + lineNumber + ": Not 4 tokens in preamble --> Skip line")
            }
          case 'e' =>
            quantifiers :+= (Formula.EXISTS, line.split(" ").tail.map(_.toInt).filterNot(_ == 0).toSet)
          case 'a' =>
            quantifiers :+= (Formula.FORALL, line.split(" ").tail.map(_.toInt).filterNot(_ == 0).toSet)
          case _ =>
            try {
              currentClause ++= line.split(" ").map(_.toInt).toSet
            } catch {
              case e: NumberFormatException => System.err.println("Line " + lineNumber + ": Number format exception --> Skip literal and rest of line")
            }
            if (currentClause.contains(0)) {
              clauseCounter += 1
              currentClause = currentClause.filterNot(_ == 0)
              varCounter ++= currentClause.map(_.abs)
              clauses :+= currentClause
              currentClause = Set[Int]()
            }
        }
      }
    }

    if (preambleRead) {
      if (numberOfClausesInPreamble != clauseCounter)
        System.err.println("Number of Clauses in Preamble: " + numberOfClausesInPreamble + ", " + "Number of computed Clauses: " + clauseCounter)
      if (numberOfVarsInPreamble != varCounter.size)
        System.err.println("Number of Vars in Preamble: " + numberOfVarsInPreamble + ", " + "Number of computed Vars: " + varCounter.size)
    }

    if (quantifiers.isEmpty) // dimacs
      (None, clauses)
    else { //qdimacs
      val unquantified = varCounter filterNot (quantifiers.map(_._2).flatten.contains(_))
      if (!unquantified.isEmpty) quantifiers +:= (Formula.EXISTS, unquantified) // prepend

      (Some(quantifiers), clauses)
    }
  }


  /**
   * Returns the number of Variables and Clauses according to the Preamble
   * @param path The path to the dimacs-file
   * @return A tupel (#Variables,#Clauses)
   */
  def numberOfVariablesAndClauses(path: String): (Int, Int) = {
    val lines = io.Source.fromFile(path).getLines()
    lines.find(_(0) == 'p') match {
      case None => (-1, -1)
      case Some(line) =>
        val tokens = line.trim.replaceAll("\\s+", " ").split(" ")
        try {
          (tokens(2).toInt, tokens(3).toInt)
        } catch {
          case _ => (-1, -1)
        }
    }
  }
}