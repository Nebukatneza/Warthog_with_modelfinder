package org.warthog.pl.knowledgecompilation

import org.warthog.pl.io.CNFUtil
import org.warthog.pl.formulas.{PLAtom, PL}
import collection.immutable.HashMap
import dnnf.simpleCompiler.dtree.{Generators => SimpleDTreeGenerator}
import dnnf.advancedCompiler.dtree.{Generators => AdvancedDTreeGenerator}
import dnnf.simpleCompiler.SimpleDNNFCompiler
import dnnf.advancedCompiler.AdvancedDNNFCompiler
import de.stzoit.prover.cnf.CNFSolver
import org.warthog.generic.parsers.DIMACSReader
import org.warthog.generic.formulas.{Xor, Not, Formula}
import org.warthog.pl.decisionprocedures.satsolver.impl.picosat.Picosat
import org.warthog.pl.decisionprocedures.satsolver.{Infinity, Duration, sat}
import sys.process.{ProcessLogger, Process}
import com.sun.jna.Platform
import java.io.File

/**
 * Contains various methods for compiling a formula or file into a DNNF
 * The compilation may either be performed by the simple or advanced compiler
 * For example there are methods for compiling:
 *  - a Formula[PL] into DNNF
 *  - a List[Set[Lit] into DNNF
 *  - a Formula[PL] into a Formula[PL] which is a DNNF
 *  - a dimacs-file into DNNF
 *  - a dimacs-file into DNNF using a specific dtree produced by c2d-compiler
 *
 * Author: hildebrandt
 * Date:
 */
package object dnnf {

  /**
   * Print information about the compilation process (recursive calls and cache hits)
   */
  val verbose = true

  sealed trait CompilerVersion
  case object Simple extends CompilerVersion
  case object Advanced extends CompilerVersion

  /**
   * Compiles a Formula[PL] into a DNNF
   * Example usage: Compile the formula "a & b | c" into DNNF using the advanced compiler:
   *    compile(Advanced, "a & b | c".pl)
   * @param version The compiler to use (Simple or Advanced)
   * @param formula The formula to compile
   * @return The corresponding d-DNNF
   */
  def compile(version: CompilerVersion, formula: Formula[PL]): DNNF = {
    val cnf = if (formula.isCNF) formula else formula.cnf
    val origClauses = CNFUtil.toList(cnf).map(_.toSet[Formula[PL]])
    var mapping = HashMap[String, Int]()
    var nextLit: Int = 1
    val clauses = origClauses.map(_.map(atom => atom match {
      case PLAtom(name) => mapping.get(name) match {
        case Some(lit) => Lit(lit, true)
        case None => mapping += (name -> nextLit); nextLit += 1; Lit(nextLit - 1, true)
      }
      case Not(PLAtom(name)) => mapping.get(name) match {
        case Some(lit) => Lit(lit, false)
        case None => mapping += (name -> nextLit); nextLit += 1; Lit(nextLit - 1, false)
      }
      case _ => throw new Exception("This should not happen!!")
    }))

    val dnnf = compile(version, clauses)

    DNNF.simplify(dnnf.substituteLits(mapping.map(_.swap)))
  }

  /** Compiles a List[Set[Int]] into a corresponding DNNF */
  def compile(version: CompilerVersion, clauses: List[Set[Lit]]): DNNF =
    if (clauses.isEmpty)
      True
    else
      version match {
      case Simple => {
        val dtree = SimpleDTreeGenerator.generateDTree(clauses)
        val compiler = new SimpleDNNFCompiler(clauses.size, dtree.varSet.size)
        val result = DNNF.simplify(compiler.cnf2Ddnnf(dtree))
        if (verbose) {println("---\nRecursive Calls: " + compiler.recursiveCalls + "\nCache Hits: " + compiler.cacheHits)}
        result
      }
      case Advanced => {
        val solverClauses = clauses map (_.map(v => CNFSolver.var2lit(v.variable, v.phase)))
        val dtree = AdvancedDTreeGenerator.generateDTree(solverClauses)
        val compiler = new AdvancedDNNFCompiler(clauses.size, dtree.varSet.size)

        if (!compiler.initSolver(solverClauses))
          False
        else {
          val result = DNNF.simplify(compiler.cnf2dnnf(dtree))
          if (verbose) {println("---\nRecursive Calls: " + compiler.recursiveCalls + "\nCache Hits: " + compiler.cacheHits)}
          result
        }

      }
  }

  /** Compiles a Formula[PL] into a corresponding Formula[PL] which is a DNNF */
  def compileToPL(version: CompilerVersion, formula: Formula[PL]) = compile(version, formula).asPLFormula


  /** Compiles a dimacs-file into a corresponding DNNF */
  //This would be nicer but does not work for whatever reasons
  //def compileDIMACS(version: CompilerVersion, file: String) = compile(version, DIMACSReader.dimacs2Clauses(file).map(_.map(l => Lit(math.abs(l), l > 0))))
  def compileDIMACS(version: CompilerVersion, file: String) = compile(version, DIMACSReader.dimacs2Formula(file))

  /**
   * Compiles a cnf from a dimacs-file into a corresponding DNNF
   * using the c2d-compiler to get the dtree.
   *
   * Currently this method will be orders of magnitude faster than
   * the other methods which use a very primitive dtree.
   *
   * Important note: This method will not be deterministic,
   * since some actions in dtree-generation are randomized.
   * So this method might create different dnnfs with each call!
   * @param version The compiler to use (Simple or Advanced)
   * @param dimacsFile The path to the dimacs-file
   * @return The corresponding DNNF
   */
  def compileWithC2DDTree(version: CompilerVersion, dimacsFile: String) = {
    val clauses = DIMACSReader.dimacs2Clauses(dimacsFile)

    version match {
      case Simple =>
        val dtree = SimpleDTreeGenerator.generateDTreeFromC2D(dimacsFile)
        val compiler = new SimpleDNNFCompiler(clauses.size, dtree.varSet.size)
        val result = DNNF.simplify(compiler.cnf2Ddnnf(dtree))
        if (verbose) {println("---\nRecursive Calls: " + compiler.recursiveCalls + "\nCache Hits: " + compiler.cacheHits)}
        result
      case Advanced =>
        val solverClauses = clauses map (_.map(v => CNFSolver.var2lit(math.abs(v), v > 0)))
        val dtree = AdvancedDTreeGenerator.generateDTreeFromC2D(dimacsFile)

        val compiler = new AdvancedDNNFCompiler(clauses.size, dtree.varSet.size)
        if (!compiler.initSolver(solverClauses))
          False
        else {
          val result = DNNF.simplify(compiler.cnf2dnnf(dtree))
          if (verbose) {println("---\nRecursive Calls: " + compiler.recursiveCalls + "\nCache Hits: " + compiler.cacheHits)}
          result
        }
    }
  }

  /**
   * Uses the c2d-Compiler to produce a DTree-file from the specified dimacs-file
   * The lines of the resulting file will be returned as an array of strings
   * (The c2d-Compiler will be interrupted after having created the dtree,
   * since there is no way to only produce the dtree-file without computing the dnnf)
   * @param dimacsFile The dimacs-file for which the dtree should be created
   * @param method The method to use for DTree-Generation, the default value is 0 which will usually yield the best results
   *               Further information can be accessed in the c2d-manual
   * @return An array of strings of the file created by the c2d-compiler
   */
  /* TODO: Think about putting this method into another package */
  /* TODO: Test this method on linux */
  def createDTreeWithC2D(dimacsFile: String, method: Int = 0): Array[String] = {
    var p : Process = null
    var dtreeCreated = false
    val log = new StringBuilder

    /** The ProcessLogger will forward the stdout-lines to this method, which will interrupt the process after the dtree is created*/
    def isFinished(line: String): Unit = {
      if (line.matches(".*Saving dtree.*done.*")) {
        dtreeCreated = true
        p.destroy
      } else {
        log.append(line+"\n")
      }
    }

    // Create the path to the c2d-compiler
    val sep = "/"
    val lib = System.getProperty("warthog.libs") + sep + "dnnf" + sep + "c2d" + sep
    val c2d =
      if (Platform.isLinux())
        lib + "linux" + sep + "c2d"
      else if (Platform.isWindows())
        lib + "win" + sep + "c2d.exe"
      else
        throw new Exception("c2d: Platform unsupported!")

    // Create and execute the process
    val builder = Process(List(c2d, "-in", dimacsFile, "-dt_method", method.toString, "-dt_out"))
    val logger = ProcessLogger(isFinished(_))
    p = builder.run(logger)

    val exit = p.exitValue // wait until process is determinated
    if (!dtreeCreated)
      throw new Exception("DTree could not be created! Exit-Value " + exit + "\n\n c2d-output:\n" + log)
    else
      if (verbose) println("DTree created.")

    val dtreeFile = dimacsFile + ".dtree"
    // c2d-compiler will always store the dtree in file "<dimacsFile>.dtree"
    val result = io.Source.fromFile(dtreeFile).getLines.drop(1).toArray
    if (!new File(dtreeFile).delete)
      println("Note: The dtree-file produced by c2d at " + dtreeFile + " could not be deleted!")
    result
  }


  /* ---------------------------------
   * Temporary test methods
   * --------------------------------- */

  /* Prints an evaluation of the compilation of the specified cnf to stdout
   *   version: 0 = all, 1 = Simple Compiler, 2 = Advanced Compiler, 3 = Advanced Compiler with C2DDTree, 5 = Simple Compiler with C2DDTree
   *   (Numbering due to "historical" reasons)
   */
  def evaluation(version: Int, dimacsFile: String, forceCounting: Boolean = false): Unit = version match {
    case 0 =>
      println("\n--- Simple ---");evaluation(1, dimacsFile);
      println("\n--- Advanced ---");evaluation(2, dimacsFile);
      println("\n--- AdvancedWithC2DDTree ---");evaluation(3, dimacsFile);
      println("\n--- SimpleWithC2DDTree ---");evaluation(5, dimacsFile);
    case _ =>
      val start = System.currentTimeMillis()
      val dnnf = version match {
        case 1 => compileDIMACS(Simple, dimacsFile)
        case 2 => compileDIMACS(Advanced, dimacsFile)
        case 3 => compileWithC2DDTree(Advanced, dimacsFile)
        case 5 => compileWithC2DDTree(Simple, dimacsFile)
        case _ => throw new Exception("Wrong call of method \"evaluation\": 0 = all, 1 = Simple Compiler, 2 = Advanced Compiler, 3 = Advanced Compiler with C2DDTree, 5 = Simple Compiler with C2DDTree")
      }
      val end = System.currentTimeMillis()

      println("Time: " + (end-start) + "ms")
      println("Nodes: " + DNNF.nodeCount(dnnf))
      println("Nodes2: " + DNNF.nodeCount2(dnnf))
      if (DNNF.nodeCount2(dnnf) < 1000000 || forceCounting) println("Models: " + DNNF.countModels(dnnf, DIMACSReader.numberOfVariablesAndClauses(dimacsFile)._1))
  }



  def getSimpleDTree(formula: Formula[PL]) = {
    val cnf = if (formula.isCNF) formula else formula.cnf
    val origClauses = CNFUtil.toList(cnf).map(_.toSet[Formula[PL]])
    var mapping = HashMap[String, Int]()

    var nextLit: Int = 1
    val clauses = origClauses.map(_.map(atom => atom match {
      case PLAtom(name) => mapping.get(name) match {
        case Some(lit) => Lit(lit, true)
        case None => mapping += (name -> nextLit); nextLit += 1; Lit(nextLit - 1, true)
      }
      case Not(PLAtom(name)) => mapping.get(name) match {
        case Some(lit) => Lit(lit, false)
        case None => mapping += (name -> nextLit); nextLit += 1; Lit(nextLit - 1, false)
      }
      case _ => throw new Exception("This should not happen!!")
    }))

    SimpleDTreeGenerator.generateDTree(clauses)
  }

  def getAdvancedDTree(formula: Formula[PL]) = {
    val cnf = if (formula.isCNF) formula else formula.cnf
    val origClauses = CNFUtil.toList(cnf).map(_.toSet[Formula[PL]])
    var mapping = HashMap[String, Int]()

    var nextLit: Int = 1
    val clauses = origClauses.map(_.map(atom => atom match {
      case PLAtom(name) => mapping.get(name) match {
        case Some(lit) => Lit(lit, true)
        case None => mapping += (name -> nextLit); nextLit += 1; Lit(nextLit - 1, true)
      }
      case Not(PLAtom(name)) => mapping.get(name) match {
        case Some(lit) => Lit(lit, false)
        case None => mapping += (name -> nextLit); nextLit += 1; Lit(nextLit - 1, false)
      }
      case _ => throw new Exception("This should not happen!!")
    }))

    val solverClauses = clauses map (_.map(v => CNFSolver.var2lit(v.variable, v.phase)))
    AdvancedDTreeGenerator.generateDTree(solverClauses)
  }

  /* Does only work with very few clauses (< 7) since Tseitin is not yet implemented */
  def checkEquality(formula: Formula[PL], dnnf: DNNF, ps: Picosat, duration: Long = -1): Int = {
    val checkFormula = Xor(formula, dnnf.asPLFormula)
    var result = 0
    sat(ps) {
      solver => {
        solver.add(checkFormula)
        result = -solver.sat(if (duration > 0) new Duration(duration) else Infinity)
      }
    }
    result
  }
}
