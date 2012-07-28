package org.warthog.pl.knowledgecompilation.dnnf

/**
 * Representation of a Bit Vector
 *
 * Author: kuebler
 * Date:
 */
class BitVec(val arr: Array[Long]) {
  private val capacity = arr.length * BitVec.LONGSIZE

  def this(capacity: Int) = this(new Array[Long](BitVec.requiredSize(capacity)))

  def this() = this(1024)

  override def hashCode = java.util.Arrays.hashCode(arr)

  private def ensure(index: Int) =
    if (index >= capacity)
      new BitVec(java.util.Arrays.copyOf(arr, BitVec.requiredSize(index)))
    else
      this

  def set(index: Int) = {
    val rv = ensure(index)
    rv.arr(index / BitVec.LONGSIZE) = rv.arr(index / BitVec.LONGSIZE) | (1L << (index % BitVec.LONGSIZE))
    rv
  }

  def unset(index: Int) = {
    val rv = ensure(index)
    rv.arr(index / BitVec.LONGSIZE) = rv.arr(index / BitVec.LONGSIZE) & ~(1L << (index % BitVec.LONGSIZE))
    rv
  }

  override def toString = arr.map(_.toBinaryString).mkString("\n")

  override def equals(that: Any) = that match {
    case bv: BitVec =>
      if (arr.length == bv.arr.length)
        (0 until arr.length).forall {
          i => arr(i) == bv.arr(i)
        }
      else
        false

    case _ => false
  }
}

object BitVec {
  val LONGSIZE = 64

  def requiredSize(index: Int) = index / LONGSIZE + 1
}