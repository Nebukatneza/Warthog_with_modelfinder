package org.warthog.pl.knowledgecompilation.dnnf.advancedCompiler

import de.stzoit.prover.dnnf.DNNFOperations
import org.warthog.pl.knowledgecompilation.dnnf._
import org.warthog.pl.knowledgecompilation.dnnf.advancedCompiler.dtree._
import de.stzoit.prover.cnf.{Clause, CNFSolver}
import scala.collection.JavaConverters._
import collection.mutable.{WeakHashMap, HashMap => MutableHashMap}


class AdvancedDNNFCompiler(numClauses: Int, numVariables: Int) {
  private val operations = new DNNFOperations

  private val andUnique = MutableHashMap[Set[DNNF], DNNF]()
  private val orUnique = MutableHashMap[Set[DNNF], DNNF]()
  private val termUnique = MutableHashMap[Set[DNNF], DNNF]()

  private val cache = new WeakHashMap[BitVec, DNNF]()

  private def lookupAnd(args: DNNF*): DNNF =
    andUnique.getOrElseUpdate(args.toSet, And(args:_*))

  private def lookupOr(args: DNNF*) =
    orUnique.getOrElseUpdate(args.toSet, Or(args:_*))

  private def lookupTerm(term: Set[DNNF]) =
    termUnique.getOrElseUpdate(term, And(term.toSeq:_*))

  private def pos(v: Int) = CNFSolver.var2lit(v, true)
  private def neg(v: Int) = CNFSolver.var2lit(v, false)
  private def neg(l: Lit) = Lit(l.variable, !l.phase)

  /**
   * Compilation routine according to A. Darwiche: "New Advances in Compiling
   * CNF to Decomposable Negation Normal Form"
   */
  def cnf2dnnf(t: DTree): DNNF = {
    trackRecursiveCall

    val sep = t.currentSeparator(operations).toList
    val term = terms(t.varSet)

    if (sep.isEmpty)
      t match {
        case DTreeLeaf(id, clause) =>
          conjoin(term, cnfAux(t))
        case DTreeNode(left, right) =>
          conjoin(term, cnfAux(left), cnfAux(right))
      }
    else {
      /* Choose the variable which appears in the largest number of unsubsumed clauses */
      /* TODO: Improve method countUnsubsumedOccirrences (current implementation is far too inefficient, especially on hard cnfs)
      val occ = t.countUnsubsumedOccurrences(operations, sep.toArray)
      val v = sep(occ.indexWhere(_ == occ.max))
      */
      val v = sep.head

      /* positive branch */
      var p: DNNF = False

      if (operations.decide(pos(v)))
        p = cnf2dnnf(t)
      operations.undoDecide(v)
      if (p == False) {
        if (operations.atAssertionLevel() && operations.assertCdLiteral())
          return cnf2dnnf(t) /* try again */
        else
          return False /* backtracking */
      }

      /* negative branch */
      var n: DNNF = False

      if (operations.decide(neg(v)))
        n = cnf2dnnf(t)
      operations.undoDecide(v)
      if (n == False) {
        if (operations.atAssertionLevel() && operations.assertCdLiteral())
          return cnf2dnnf(t) /* try again */
        else
          return False /* backtracking */
      }

      conjoin(term, disjoin(conjoin(Lit(v, true), p), conjoin(Lit(v, false), n)))
    }
  }

  private def conjoin(term: Set[DNNF], shannonExpansion: DNNF): DNNF = {
    val termAnd = lookupTerm(term)

    if (termAnd == And() || termAnd == True)
      shannonExpansion
    else if (termAnd == False || shannonExpansion == False)
      False
    else
      lookupAnd(termAnd, shannonExpansion)
  }

  /*
   * This method will conjoin term (all newly implied literals) and left and right DNNF
   * Note that left and right are call-by-name parameters, so they will only be evaluated if necessary
   * This is strongly required, since otherwise backtracking will cause errors
   */
  private def conjoin(term: Set[DNNF], left: => DNNF, right: => DNNF): DNNF = {
    val termsAnd = lookupTerm(term)
    lazy val leftDnnf = left    // left and right should be evaluated only once
    lazy val rightDnnf = {
      terms(Set[Int]())   // TODO: Explain this!!
      right
    }

    if (termsAnd == False || leftDnnf == False || rightDnnf == False)
      False
    else
      lookupAnd(termsAnd, leftDnnf, rightDnnf)
  }

  private def conjoin(lit: DNNF, fm: DNNF): DNNF = lookupAnd(lit, fm)

  private def disjoin(left: DNNF, right: DNNF): DNNF = lookupOr(left, right)

  /**
   * compute all newly implied literals that intersect with the variable set vs
   *
   * @param vs variable set to compute intersection of unit implied literals with
   * @return set of newly implied literals
   */
  private def terms(vs: Set[Int]): Set[DNNF] =
    operations.newlyImplied().asScala.toSet.map((x: java.lang.Integer) => x.toInt).
      filter(x => vs.contains(x / 2)).map((x: Int) => Lit(x / 2, x % 2 == 1))

  /**
   * Auxillary method for cnf to dnnf-compilation: generate dnnf for clauses
   * if at leaf or lookup &/ update cache for inner node
   *
   * @param t DTree to compile
   * @return compilation result
   */
  private def cnfAux(t: DTree): DNNF = t match {
    case DTreeLeaf(_, clause) => clauseToDDNNF(clause)
    case _ => // t: DTreeNode
      val key = computeCacheKey(t.currentClauseIds(operations), t.varSet)
      cache.get(key) match {
        case Some(v) => trackHit; v
        case None =>
          val r = cnf2dnnf(t)
          if (r != False)
            cache.put(key, r)
          r
      }
  }

  var cacheHits: Long = 0L
  private def trackHit = {
    cacheHits += 1
    if (verbose && (cacheHits < 100000 && cacheHits % 1000 == 0 || cacheHits % 10000 == 0))
      println("tracked cache hits: " + cacheHits)
  }

  var recursiveCalls = 0L
  private def trackRecursiveCall = {
    recursiveCalls += 1
    if (verbose && (recursiveCalls < 100000 && recursiveCalls % 1000 == 0 || recursiveCalls % 10000 == 0))
      println("recursive calls of cnf2Ddnnf: " + recursiveCalls)
  }

  /**
   * Compute a cache key as described in "New Advances in CNF to Decomposable
   * Negation Normal Form": Key is made up of a bit vector in which for each
   * unsubsumed clause and each instantiated variable a binary flag is set.
   *
   * @param clauseIds unsubsumed clauses
   * @param varSet variable set to scan for instantiated entries
   * @return generated cache key
   */
  private def computeCacheKey(clauseIds: Set[Int], varSet: Set[Int]) = {
    val key = new BitVec(numClauses + numVariables)

    for (cls <- clauseIds)
      key.set(cls)
    for (v <- varSet if operations.lit2variable(2 * v).get_value() != CNFSolver.Val.UNKNOWN)
      key.set(v + numClauses)

    key
  }

  /**
   * Transform a single Clause to d-DNNF (i.e. -1 2 -3 gets
   * (-1 | (2 & 1) | (-3 & 1 & -2))), return True if clause is
   * (unit-) subsumed
   */
  def clauseToDDNNF(clause: Set[Int]) = {
    val nonsubsumedClause: Option[List[Int]] = //nonsubsumed(false, List.empty[Int], clause.toList)
      if (clause.exists(operations.lit2val(_) == CNFSolver.Val.TRUE))
        None
      else
        Some(clause.toList.filter(operations.lit2val(_) == CNFSolver.Val.UNKNOWN))

    if (nonsubsumedClause.isDefined) {
      //clauseToDDNNFAux(nonsubsumedClause.get, Nil, Nil)
      val lits = nonsubsumedClause.get.map(l => Lit(l / 2, (l % 2 == 1)))
      val ands = lits.foldLeft[List[List[Lit]]](List(List()))((as, lit) => as ++ List(as.takeRight(1).head ++ List(neg(lit))))
      Or(lits.zip(ands).map(t => And((List(t._1) ++ t._2): _*)): _*)
    }
    else
      True
  }

  /*
   * TODO:
   * =====
   *
   *   Initialisation:
   *     - Initialize SAT Solver with clause set
   *     - Build a DTree from the clause set (optionally parse a externaly generated)
   */
  def initSolver(clauses: List[Set[Int]]): Boolean = {
    for (i <- 1 to numVariables)
      operations.newVariable(i.toString)
    for (clause <- clauses) {
      val solverClause = new Clause(operations)

      for (lit <- clause)
        solverClause.push((if (lit % 2 == 1) "" else "-") + (lit / 2))

      if (!operations.pushClause(solverClause))
        return false
    }
    operations.bcp()
  }
}