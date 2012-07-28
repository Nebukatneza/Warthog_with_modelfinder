package org.warthog.pl.knowledgecompilation.dnnf

import org.warthog.generic.formulas._
import org.warthog.pl.formulas.{PLAtom, PL}
import java.util.IdentityHashMap
import collection.JavaConversions

/**
 * Representation of a DNNF
 *
 * Author: hildebrandt
 * Date:
 */
trait DNNF {
  /** Converts this DNNF to a Formula[PL] */
  def asPLFormula: Formula[PL]

  /** Performs a substitution this DNNF */
  def substituteLits(mapping: Map[Int, String]): DNNF
}

case object True extends DNNF {
  override def toString = "True"
  override def hashCode = 1

  def asPLFormula = Verum[PL]

  def substituteLits(mapping: Map[Int, String]) = True
}

case object False extends DNNF {
  override def toString = "False"
  override def hashCode = 2

  def asPLFormula = Falsum[PL]

  def substituteLits(mapping: Map[Int, String]) = False
}

case class And(var operands: DNNF*) extends DNNF {
  /** ID for this node, used for hashCode-Implementation */
  private val ID = DNNF.getNextAndID
  override def hashCode = ID
  override def equals(obj: Any) = obj match {
    case obj: And => this.ID == obj.ID //And(ops@_*) => ops.length == operands.length && ops.forall(operands.contains(_))
    case _ => false
  }

  override def toString =
    if (DNNF.nodeCount(this) <= 100)
      "AND(" + operands.mkString(",") + ")"
    else
      "DNNF with more than 100 nodes"

  def asPLFormula = org.warthog.generic.formulas.And[PL](operands.map(_.asPLFormula): _*)

  /* Only operands are changed so that no new Instance is created */
  def substituteLits(mapping: Map[Int, String]) = {operands = operands.map(_.substituteLits(mapping)):_*; this}
}

case class Or(var operands: DNNF*) extends DNNF {
  /** ID for this node, used for hashCode-Implementation */
  private val ID = DNNF.getNextOrID
  override def hashCode = ID
  override def equals(obj: Any) = obj match {
    case obj: Or => this.ID == obj.ID //Or(ops@_*) => ops.length == operands.length && ops.forall(operands.contains(_))
    case _ => false
  }

  override def toString =
    if (DNNF.nodeCount(this) <= 100)
      "OR(" + operands.mkString(",") + ")"
    else
      "DNNF with more than 100 nodes"

  def asPLFormula = org.warthog.generic.formulas.Or[PL](operands.map(_.asPLFormula): _*)

  /* Only operands are changed so that no new Instance is created */
  def substituteLits(mapping: Map[Int, String]) = {operands = operands.map(_.substituteLits(mapping)):_*; this}
}

case class Lit(variable: Int, phase: Boolean) extends DNNF {
  override def toString = (if (phase) "" else "-") + variable
  override def equals(obj: Any) = obj match {
    case Lit(v,p) => v == variable && p == phase
    case _ => false
  }

  def asPLFormula = throw new Exception("Cannot convert Int-Literal into PL")

  def substituteLits(mapping: Map[Int, String]) = StringLit(mapping.getOrElse(variable, variable.toString), phase)
}

case class StringLit(variable: String, phase: Boolean) extends DNNF {
  override def toString = (if (phase) "" else "-") + variable
  override def equals(obj: Any) = obj match {
    case StringLit(v,p) => v == variable && p == phase
    case _ => false
  }

  def asPLFormula = if (phase) PLAtom(variable) else Not(PLAtom(variable))

  def substituteLits(mapping: Map[Int, String]) = this
}


/**
 * This companion object contains many operations for dnnfs,
 * like counting nodes, simplification, model counting, restriction, projection,...
 */
object DNNF {
  /**
   * Used for hashCode-Implementation
   */
  private var nextAndID = 3
  private var nextOrID = 3
  def getNextAndID = {nextAndID += 1; nextAndID}
  def getNextOrID = {nextOrID += 1; nextOrID}

  /**
   * Negate literals
   */
  def neg(lit: Lit) = Lit(lit.variable, !lit.phase)
  def neg(atom: StringLit) = StringLit(atom.variable, !atom.phase)

  /**
   * Returns the variable set of a given dnnf as set of strings
   * @param dnnf The dnnf
   * @return The variable set of the dnnf
   */
  def varSet(dnnf: DNNF): Set[String] = dnnf match {
    case And(args@_*) => args.map(varSet).foldLeft(Set[String]())((a,b) => a union b)
    case Or(args@_*) => args.map(varSet).foldLeft(Set[String]())((a,b) => a union b)
    case Lit(v, _) => Set(v.toString)
    case StringLit(v, _) => Set(v)
    case _ => Set()
  }

  /**
   * Returns the variable set of a given dnnf as set of ints
   * Will throw an exception if the dnnf contains a StringLit
   * @param dnnf The dnnf
   * @return The variable set of the dnnf
   */
  def intVarSet(dnnf: DNNF): Set[Int] = dnnf match {
    case And(args@_*) => args.map(intVarSet).foldLeft(Set[Int]())((a,b) => a union b)
    case Or(args@_*) => args.map(intVarSet).foldLeft(Set[Int]())((a,b) => a union b)
    case Lit(v, _) => Set(v)
    case StringLit(v, _) => throw new Exception("StringLit found!")
    case _ => Set()
  }

  /**
   * Returns the total count of nodes in the dnnf (each node is only counted once!)
   * @param dnnf The dnnf
   * @return The node count
   */
  def nodeCount(dnnf: DNNF): Long = {
    val seen = collection.mutable.Set[Int]()
    def cnt(dnnf: DNNF): Long =
      if (seen.contains(System.identityHashCode(dnnf))) // node already visited
        0
      else {
        seen.add(System.identityHashCode(dnnf))
        dnnf match {
          case And(args@_*) => args.foldLeft(1L)(_ + cnt(_))
          case Or(args@_*)  => args.foldLeft(1L)(_ + cnt(_))
          case _            => 1
        }
      }
    cnt(dnnf)
  }

  /**
   * Returns the total count of nodes in the dnnf
   * Each node may be counted several times
   * @param dnnf The dnnf
   * @return The node count
   */
  def nodeCount2(dnnf: DNNF): Long = dnnf match {
    case And(args@_*) => args.foldLeft(1L)(_ + nodeCount2(_))
    case Or(args@_*)  => args.foldLeft(1L)(_ + nodeCount2(_))
    case _            => 1
  }


  /**
   * Simplifies a dnnf:
   *   1) Removes boolean constants
   *   2) Replaces empty inner nodes by the corresponding boolean constant (-> 1)
   *   3) Replaces nodes with only one child by this child
   *   4) "Flattens" inner nodes, for example if an or-node A has another or-node B as
   *       child, the children of B will be pulled up to A (same for and-nodes)
   * @param dnnf The dnnf
   * @return A simplified version of the dnnf
   */
  def simplify(dnnf: DNNF): DNNF = {
    val seen = JavaConversions.mapAsScalaMap[DNNF, DNNF](new IdentityHashMap[DNNF, DNNF])

    def simp(dnnf: DNNF): DNNF = seen.getOrElseUpdate(dnnf, dnnf match {
      case And(args@_*) =>
        val simplifiedArgs = args.map(simp(_)).map(arg => arg match {
          case And(as@_*) => as
          case True => List()
          case _ => List(arg)
        }).flatten
        if (simplifiedArgs.contains(False))
          False
        else
          simplifiedArgs.size match {
            case 0 => True
            case 1 => simplifiedArgs.head
            case _ => And(simplifiedArgs:_*)
          }
      case Or(args@_*) =>
        val simplifiedArgs = args.map(simp(_)).map(arg => arg match {
          case Or(as@_*) => as
          case False => List()
          case _ => List(arg)
        }).flatten

        if (simplifiedArgs.contains(True))
          True
        else
          simplifiedArgs.size match {
            case 0 => False
            case 1 => simplifiedArgs.head
            case _ => Or(simplifiedArgs:_*)
          }
      case _ => dnnf
    })

    simp(dnnf)
  }



  /*
   * Implementations according to
   * Adnan Darwiche, "Decomposable negation normal form" (2001)
   */

  /**
   * Is a given dnnf satisfiable?
   * @param dnnf The dnnf
   * @return True, if the dnnf is satisfiable
   */
  def sat(dnnf: DNNF): Boolean = dnnf match {
    case True => true
    case False => false
    case Lit(_, _) => true
    case StringLit(_, _) => true
    case And(args@_*) => args.forall(sat(_))
    case Or(args@_*) => args.exists(sat(_))
  }

  /**
   * Restricts a dnnf with the given literals (StringLits)
   * @param dnnf A dnnf
   * @param omega A set of literals
   * @return The dnnf restricted to the literals of omega
   */
  def restrict(dnnf: DNNF, omega: Set[StringLit]): DNNF = dnnf match {
    case dnnf: StringLit =>
      if (omega.contains(dnnf))
        True
      else if (omega.contains(neg(dnnf)))
        False
      else
        dnnf
    case And(args@_*) => simplify(And(args.map(restrict(_, omega)): _*))
    case Or(args@_*) => simplify(Or(args.map(restrict(_, omega)): _*))
    case _ => dnnf
  }

  /**
   * Projects a dnnf to the given literals
   * @param dnnf A dnnf
   * @param omega A set of literals
   * @return The dnnf projected to the literals of omega
   */
  def project(dnnf: DNNF, omega: Set[StringLit]): DNNF = dnnf match {
    case dnnf: StringLit =>
      if (!(omega.contains(dnnf) || omega.contains(neg(dnnf))))
        True
      else
        dnnf
    case And(args@_*) => simplify(And(args.map(project(_, omega)): _*))
    case Or(args@_*) => simplify(Or(args.map(project(_, omega)): _*))
    case _ => dnnf
  }


  /**
   * Computes the Minimum Cardinality of a dnnf
   * Returns None if the dnnf is unsatisfiable
   * @param dnnf The dnnf
   * @return The Minimum Cardinality of the dnnf
   */
  def minCardinality(dnnf: DNNF): Option[Long] = dnnf match {
    case True => Some(0)
    case False => None
    case Lit(_, phase) => if (phase) Some(0) else Some(1)
    case StringLit(_, phase) => if (phase) Some(0) else Some(1)
    case And(args@_*) => args.foldLeft[Option[Long]](Some(0))((n, arg) =>
      (n, minCardinality(arg)) match {
        case (Some(i), Some(j)) => Some(i + j)
        case _ => None
      })
    case Or(args@_*) => args.map(minCardinality(_)).foldLeft[Option[Long]](None)((n, m) =>
      (n, m) match {
        case (Some(i), Some(j)) => Some(scala.math.min(i, j))
        case (Some(i), _) => Some(i)
        case (_, j) => j
      })
  }



  /**
   * Smoothes a dnnf
   * Citation from Adnan Darwitche: On the Tractable Counting of Theory Models and its Application to Truth Maintenance and Belief Revision
   * "For each disjunction a = a_1 | ... | a_n, if atoms(a_i) != atoms(a) we can replace the disjunct a_i in a with
   *    a_i & AND_(A € S){A | -A}  where S = atoms(a) - atoms(a_i) "
   * @param dnnf The dnnf
   * @return A smoothed version of the dnnf
   */
  def smooth(dnnf: DNNF): DNNF = {
    val seen = JavaConversions.mapAsScalaMap[DNNF, DNNF](new IdentityHashMap[DNNF, DNNF])
    def smoo(dnnf: DNNF): DNNF = seen.getOrElseUpdate(dnnf, dnnf match {
      case Or(args@_*) =>
        val atoms = varSet(dnnf)
        Or(args.map(arg =>
          smoo(And((List(arg) ++ (atoms -- varSet(arg)).map(a => Or(StringLit(a, true), StringLit(a, false)))):_*))):_*)
      case And(args@_*) => And(args.map(smoo):_*)
      case other => other
    })
    smoo(dnnf)
  }

  /* For debugging */
  private def isSmooth(dnnf: DNNF): Boolean = dnnf match {
    case Or(args@_*) => args.map(varSet(_)).forall(_ == varSet(args.head)) && args.foldLeft(true)(_ && isSmooth(_))
    case And(args@_*) => args.foldLeft(true)(_ && isSmooth(_))
    case _ => true
  }

  /**
   * A method for model counting
   * According to Adnan Darwitche: "On the Tractable Counting of Theory Models and its Application to Truth Maintenance and Belief Revision"
   * each or-node in a sd-DNNF corresponds to a + and each and-node corresponds to a *
   * @param dnnf The d-DNNF whose model should be counted
   * @param vars The number of variables of the dnnf (better: of the original formula!)
   * @return The number of models of the specified d-DNNF
   */
  def countModels(dnnf: DNNF, vars: Int): BigInt = {
    val seen = JavaConversions.mapAsScalaMap[DNNF, BigInt](new IdentityHashMap[DNNF, BigInt])
    def count(dnnf: DNNF): BigInt = seen.getOrElseUpdate(dnnf, dnnf match {
      case Or(args@_*)    => args.foldLeft(BigInt(0))(_ + count(_))
      case And(args@_*)   => if(args.isEmpty) BigInt(0) else args.foldLeft(BigInt(1))(_ * count(_))
      case StringLit(_,_) => BigInt(1)
      case Lit(_,_)       => BigInt(1)
      case _              => throw new Exception("DNNF still contains boolean constants, please simplify before counting models!")
    })
    val smoothed = smooth(dnnf)
    //if (!isSmooth(smoothed)) println("Not smooth!!")  /* Debugging */
    count(smoothed) * BigInt(2).pow(vars - DNNF.varSet(smoothed).size)
  }

  /* Temporary test method */
  def isDecomposable(dnnf: DNNF): Boolean = {
    val seen = JavaConversions.mapAsScalaMap[DNNF, Boolean](new IdentityHashMap[DNNF, Boolean])
    def isDec(dnnf: DNNF): Boolean = seen.getOrElseUpdate(dnnf, dnnf match {
      case Or(args@_*)    => args.foldLeft(true)(_ && isDec(_))
      case And(args@_*)   =>
        for (i <- 0 until args.size)
          for (j <- i+1 until args.size)
            if (DNNF.varSet(args(i)).intersect(DNNF.varSet(args(j))).nonEmpty) {
              println(DNNF.varSet(args(i)).intersect(DNNF.varSet(args(j))))
              return false
            }
        args.foldLeft(true)(_ && isDec(_))
      case _              => true
    })
    isDec(dnnf)
  }
}