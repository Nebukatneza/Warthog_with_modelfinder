package de.stzoit.prover.collections.nativeType;

import java.util.Arrays;

/**
 * Remove generic types in order to speed up computation by avoiding (auto-) 
 * boxing to/from java.lang.Boolean
 * 
 * @author ak
 */
/**
 * Simple but efficient vector implementation, based on the vector
 * implementation available in MiniSAT. Note that the elements are compared
 * using their references, not using the equals method.
 * 
 * @author leberre
 */
public class BooleanVec {
	// MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson
	//
	// Permission is hereby granted, free of charge, to any person obtaining a
	// copy of this software and associated documentation files (the
	// "Software"), to deal in the Software without restriction, including
	// without limitation the rights to use, copy, modify, merge, publish,
	// distribute, sublicense, and/or sell copies of the Software, and to
	// permit persons to whom the Software is furnished to do so, subject to
	// the following conditions:
	//
	// The above copyright notice and this permission notice shall be included
	// in all copies or substantial portions of the Software.
	//
	// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
	// OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
	// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
	// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
	// LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
	// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
	// WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

	@SuppressWarnings("unused")
	private static final long serialVersionUID = 1L;

	/**
	 * Create a Vector with an initial capacity of 5 elements.
	 */
	public BooleanVec() {
		this(5);
	}

	/**
	 * Adapter method to translate an array of int into an IVec.
	 * 
	 * The array is used inside the Vec, so the elements may be modified outside
	 * the Vec. But it should not take much memory. The size of the created Vec
	 * is the length of the array.
	 * 
	 * @param elts
	 *            a filled array of T.
	 */
	public BooleanVec(boolean[] elts) {
		// DLB findbugs ok
		myarray = elts;
		nbelem = elts.length;
	}

	/**
	 * Create a Vector with a given capacity.
	 * 
	 * @param size
	 *            the capacity of the vector.
	 */
	public BooleanVec(int size) {
		myarray = (boolean[]) new boolean[size];
	}

	/**
	 * Construit un vecteur contenant de taille size rempli a l'aide de size
	 * pad.
	 * 
	 * @param size
	 *            la taille du vecteur
	 * @param pad
	 *            l'objet servant a remplir le vecteur
	 */
	public BooleanVec(int size, boolean pad) {
		myarray = (boolean[]) new boolean[size];
		for (int i = 0; i < size; i++) {
			myarray[i] = pad;
		}
		nbelem = size;
	}

	public int size() {
		return nbelem;
	}

	/**
	 * Remove nofelems from the Vector. It is assumed that the number of
	 * elements to remove is smaller or equals to the current number of elements
	 * in the vector
	 * 
	 * @param nofelems
	 *            the number of elements to remove.
	 */
	public void shrink(int nofelems) {
		// assert nofelems <= nbelem;
		while (nofelems-- > 0) {
			myarray[--nbelem] = false;
		}
	}

	/**
	 * reduce the Vector to exactly newsize elements
	 * 
	 * @param newsize
	 *            the new size of the vector.
	 */
	public void shrinkTo(final int newsize) {
		// assert newsize <= size();
		for (int i = nbelem; i > newsize; i--) {
			myarray[i - 1] = false;
		}
		nbelem = newsize;
		// assert size() == newsize;
	}

	/**
	 * Pop the last element on the stack. It is assumed that the stack is not
	 * empty!
	 */
	public void pop() {
		// assert size() > 0;
		myarray[--nbelem] = false;
	}

	public void growTo(final int newsize, final boolean pad) {
		// assert newsize >= size();
		ensure(newsize);
		for (int i = nbelem; i < newsize; i++) {
			myarray[i] = pad;
		}
		nbelem = newsize;
	}

	public void ensure(final int nsize) {
		if (nsize >= myarray.length) {
			boolean[] narray = (boolean[]) new boolean[Math.max(nsize, nbelem * 2)];
			System.arraycopy(myarray, 0, narray, 0, nbelem);
			myarray = narray;
		}
	}

	public BooleanVec push(final boolean elem) {
		ensure(nbelem + 1);
		myarray[nbelem++] = elem;
		return this;
	}

	public void unsafePush(final boolean elem) {
		myarray[nbelem++] = elem;
	}

	/**
	 * Insert an element at the very begining of the vector. The former first
	 * element is appended to the end of the vector in order to have a constant
	 * time operation.
	 * 
	 * @param elem
	 *            the element to put first in the vector.
	 */
	public void insertFirst(final boolean elem) {
		if (nbelem > 0) {
			push(myarray[0]);
			myarray[0] = elem;
			return;
		}
		push(elem);
	}

	public void insertFirstWithShifting(final boolean elem) {
		if (nbelem > 0) {
			ensure(nbelem + 1);
			for (int i = nbelem; i > 0; i--) {
				myarray[i] = myarray[i - 1];
			}
			myarray[0] = elem;
			nbelem++;
			return;
		}
		push(elem);
	}

	public void clear() {
		Arrays.fill(myarray, 0, nbelem, false);
		nbelem = 0;
	}

	/**
	 * return the latest element on the stack. It is assumed that the stack is
	 * not empty!
	 * 
	 * @return the last element on the stack (the one on the top)
	 */
	public boolean last() {
		// assert size() != 0;
		return myarray[nbelem - 1];
	}

	public boolean get(final int index) {
		return myarray[index];
	}

	public void set(int index, boolean elem) {
		if (0<=index)
			myarray[index] = elem;
	}

	/**
	 * Remove an element that belongs to the Vector. The method will break if
	 * the element does not belong to the vector.
	 * 
	 * @param elem
	 *            an element from the vector.
	 */
	public void remove(boolean elem) {
		// assert size() > 0;
		int j = 0;
		for (; myarray[j] != elem; j++) {
			assert j < size();
		}
		// arraycopy is always faster than manual copy
		System.arraycopy(myarray, j + 1, myarray, j, size() - j - 1);
		myarray[--nbelem] = false;
	}

	/**
	 * Delete the ith element of the vector. The latest element of the vector
	 * replaces the removed element at the ith indexer.
	 * 
	 * @param index
	 *            the indexer of the element in the vector
	 * @return the former ith element of the vector that is now removed from the
	 *         vector
	 */
	public boolean delete(int index) {
		// assert index >= 0 && index < nbelem;
		boolean ith = myarray[index];
		myarray[index] = myarray[--nbelem];
		myarray[nbelem] = false;
		return ith;
	}

	/**
	 * Ces operations devraient se faire en temps constant. Ce n'est pas le cas
	 * ici.
	 * 
	 * @param copy
	 */
	public void copyTo(BooleanVec copy) {
		final BooleanVec ncopy = (BooleanVec) copy;
		final int nsize = nbelem + ncopy.nbelem;
		copy.ensure(nsize);
		System.arraycopy(myarray, 0, ncopy.myarray, ncopy.nbelem, nbelem);
		ncopy.nbelem = nsize;
	}

	/**
	 * @param dest
	 */
	public void copyTo(int[] dest) {
		// assert dest.length >= nbelem;
		System.arraycopy(myarray, 0, dest, 0, nbelem);
	}

	/*
	 * Copy one vector to another (cleaning the first), in constant time.
	 */
	public void moveTo(BooleanVec dest) {
		copyTo(dest);
		clear();
	}

	public void moveTo(int dest, int source) {
		if (dest != source) {
			myarray[dest] = myarray[source];
			myarray[source] = false;
		}
	}

	public boolean[] toArray() {
		// DLB findbugs ok
		return myarray;
	}
	
	public boolean[] toArray(boolean[] a) {
		int size=size();
		boolean[] r=a.length>=size ? a 
		                     : (boolean[])java.lang.reflect.Array.newInstance(a.getClass().getComponentType(), size);
		for (int i=0; i<r.length; i++)
			if (i<myarray.length) {
				r[i]=(boolean)myarray[i];
			} else
				break;
		return r;
	}

	private int nbelem;

	private boolean[] myarray;

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuffer stb = new StringBuffer();
		for (int i = 0; i < nbelem - 1; i++) {
			stb.append(myarray[i]);
			stb.append(","); //$NON-NLS-1$
		}
		if (nbelem > 0) {
			stb.append(myarray[nbelem - 1]);
		}
		return stb.toString();
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (obj instanceof BooleanVec) {
			BooleanVec v = (BooleanVec) obj;
			if (v.size() != size())
				return false;
			for (int i = 0; i < size(); i++) {
				if (v.get(i) != get(i)) {
					return false;
				}
			}
			return true;
		}
		return false;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		int sum = 0;
		for (int i = 0; i < nbelem; i++) {
			sum += new Boolean(myarray[i]).hashCode() / nbelem;
		}
		return sum;
	}

	public boolean isEmpty() {
		return nbelem == 0;
	}

	/**
	 * @since 2.1
	 */
	public boolean contains(boolean e) {
		for (int i = 0; i < nbelem; i++) {
			//if (myarray[i].equals(e)) // changed by MS
			if (myarray[i] == e)
				return true;
		}
		return false;
	}
}
