package de.stzoit.prover.collections;

import java.io.PrintStream;
import java.lang.reflect.Array;
import java.util.Arrays;

public class Heap<T extends Comparable<T>> {
	protected T[] heap=null;
	protected int heapsize=0;
	protected boolean maybe_inconsistent=false;
	
	public Heap() {
	}
	
	public Heap(T[] array) {
		heap=array;
		if (heap!=null) {
			heapsize=heap.length;
			restoreHeapProperty();
		}
	}
	
	public int size() {
		return heapsize;
	}
	
	public void clear() {
		try {
			if (heap!=null)
				Arrays.fill(heap, 0, heapsize, null);
			heapsize=0;
		} catch (Throwable t) {
			t.printStackTrace();
		}
	}
	
	@SuppressWarnings("unchecked")
	public void insert(T a) {
		if (maybe_inconsistent)
			quickInsert(a);
		else {
			heapsize++;
			if (heap==null || heap.length<heapsize) {
				T[] _heap=(T[])Array.newInstance(a.getClass(), (heap==null ? 2 : heap.length*2));
				if (heap!=null)
					System.arraycopy(heap, 0, _heap, 0, heap.length);
				heap=_heap;
			}
			heap[heapsize-1]=a;
			heapIncreaseKey(heapsize-1);
		}
	}
	
	@SuppressWarnings("unchecked")
	public void quickInsert(T a) {
		if (!maybe_inconsistent)
			maybe_inconsistent=true;
		heapsize++;
		if (heap==null || heap.length<heapsize) {
			T[] _heap=(T[])Array.newInstance(a.getClass(), (heap==null ? 2 : heap.length*2));
			if (heap!=null)
				System.arraycopy(heap, 0, _heap, 0, heap.length);
			heap=_heap;
		}
		heap[heapsize-1]=a;
	}
	
	/* might destroy heap property */
	protected void quickDelete(int index) {
		if (heapsize<1 || index<0 || heapsize<=index)
			return;
		if (!maybe_inconsistent)
			maybe_inconsistent=true;
		if (index==heapsize-1)
			heapsize--;
		else {
			heap[index]=heap[heapsize-1];
			heapsize--;
		}
	}
	
	public void quickDelete(T a) {
			quickDelete(find(a));
	}
	
	public void restoreHeapProperty() {
		if (heapsize>0) {
			for (int i=parentInd(heapsize-1); i>=0; i--)
				maxHeapify(i);
		}
		/* clear maybe_inconsistent flag */
		maybe_inconsistent=false;
	}
	
	protected void delete(int index) {
		if (maybe_inconsistent)
			quickDelete(index);
		else {
			if (heapsize<1 || index<0 || heapsize<=index)
				return;

			if (index==heapsize-1)
				heapsize--;
			else {
				T old=heap[index];
				heap[index]=heap[heapsize-1];
				if (heapsize>1) {
					heapsize--;
					if (heap[index].compareTo(old)>0)
						heapIncreaseKey(index);
					else
						heapDecreaseKey(index);
				} else
					heapsize=0;
			}
		}
	}
	
	public void delete(T a) {
		int l=find(a);
		delete(l);
	}
	
	public void delete(T a, Object r) { /* guarded, will complain if delete failed */
		if (maybe_inconsistent)
			restoreHeapProperty();
		int l=find(a);
		if (r!=null && l<0) {
			System.out.print("failed to delete "+a+" from varq (find returned "+l+"), varq is ");
			consistent();
			this.print(System.out);
		}
		if (!consistent()) {
			System.out.println("inconsistent before deletion");
		}
		T old=null, _new=null, _nnew=null;
		if (l>=0) {
			old=heap[l];
			_new=heap[heapsize-1];
		}
		delete(l);
		if (l<heapsize && l>=0)
			_nnew=heap[l];
		if (!consistent()) {
			System.out.println("inconsistent after deletion, old: "+old+", swapped: "+_new+", inpos: "+_nnew);
			print(System.out);
		}
	}
	
	protected int find(T a, int index) {
		if (heapsize<1 || a==null)
			return -1;
		else if (index<heapsize) {
			if (heap[index]==a)
				return index;
			else {
				/* additional checking hopefully speeds up searching in most cases */
				/* both branches don't apply */
				if (   leftInd(index)<heapsize && left(index).compareTo(a)<0 
						&& rightInd(index)<heapsize && right(index).compareTo(a)<0) {
					return -1;	
				}
				/* left branch doesn't apply */
				if (leftInd(index)<heapsize && left(index).compareTo(a)<0) {
					return find(a, rightInd(index));
				}
				/* right branch doesn't apply */
				if (rightInd(index)<heapsize && right(index).compareTo(a)<0) {
					return find(a, leftInd(index));
				}

				/* both branches qualify, search left first */
				int l=find(a, leftInd(index));
				return ((l<0) ? find(a, rightInd(index)) : l);
			}
		}
		return -1;
	}
	
	private int secureButSlowFind(T a, int index) {
		if (heapsize<1 || a==null)
			return -1;
		else if (index<heapsize) {
			if (heap[index]==a)
				return index;
			else {
				int l=secureButSlowFind(a, leftInd(index));
				return (l<0) ? secureButSlowFind(a, rightInd(index)) : l;
			}
		}
		return -1;
	}
	
	public boolean consistent() {
		for (int i=0; i<heapsize; i++)
			if (!consistent(i))
				return false;
		return true;
	}
	
	private boolean consistent(int i) {
		if (leftInd(i)<heapsize && left(i).compareTo(heap[i])>0)
			return false;
		if (rightInd(i)<heapsize && right(i).compareTo(heap[i])>0)
			return false;
		return true;
	}
	
	public int find(T a) {
		return find(a, 0);
	}
	
	public T heapExtractMax() {
		if (heapsize<1)
			return null;
		if (maybe_inconsistent) { /* restore heap property destroyed by quick_{delete,insert} */
			restoreHeapProperty();
			maybe_inconsistent=false;
		}

		T max=heap[0];
		if (heapsize>1) { /* no need*/
			heap[0]=heap[heapsize-1];
			heapsize--;
			heapDecreaseKey(0);
		} else /* heapsize==1 */
			heapsize=0;
		return max;
	}
	
	/* get max. element without removing it */
	public T peek() {
		if (heapsize<1)
			return null;
		if (maybe_inconsistent) {
			restoreHeapProperty();
			maybe_inconsistent=false;
		}
		return heap[0];
	}
	
	public void heapIncreaseKey(T a) {
		if (!maybe_inconsistent)
			heapIncreaseKey(find(a));
	}
	
	protected void heapIncreaseKey(int index) {
		int i=index;
		while (i>0 && parent(i).compareTo(heap[i])<0) {
			swap(parentInd(i), i);
			i=parentInd(i);
		}
	}
	
	public void heapDecreaseKey(T a) {
		if (!maybe_inconsistent)
			heapDecreaseKey(find(a));
	}
	
	protected void heapDecreaseKey(int index) {
		maxHeapify(index);
	}
	
	/* e.g. left(0)=heap[1], left(1)=heap[3], left(2)=heap[5], ... */
	public T left(int index) {
		return heap[leftInd(index)];
	}
	
	private int leftInd(int index) {
		return ((index+1)<<1)-1;
	}
	
	/* e.g. right(0)=heap[2], right(1)=heap[4], right(2)=heap[6], ... */
	public T right(int index) {
		return heap[rightInd(index)];
	}
	
	private int rightInd(int index) {
		return ((index+1)<<1);
	}
	
	/* e.g. parent(0)=0, parent(1)=0, parent(2)=0, parent(3)=1, parent(4)=1, parent(5)=2, ... */
	public T parent(int index) {
		return heap[parentInd(index)];
	}
	
	protected int parentInd(int index) {
		return ((index+1)>>>1)-1;
	}
	
	private void maxHeapify(int index) {
		if (index<0)
			return;

		int largest;

		if (leftInd(index)<heapsize && left(index).compareTo(heap[index])>0)
			largest=leftInd(index);
		else
			largest=index;

		if (rightInd(index)<heapsize && right(index).compareTo(heap[largest])>0)
			largest=rightInd(index);

		if (largest!=index) {
			swap(index, largest);
			maxHeapify(largest);
		}
	}
	
	protected void swap(int pos0, int pos1) {
		if (pos0!=pos1 && pos0<heapsize && pos1<heapsize) {
			T tmp=heap[pos0];
			heap[pos0]=heap[pos1];
			heap[pos1]=tmp;
		}
	}
	
	public T get(int i) {
		if (i<heapsize)
			return heap[i];
		return null;
	}
	
	public void print(PrintStream out) {
		for (int i=0; i<heapsize; i++)
			out.print(heap[i]+" ");
		out.print("\n");
		out.flush();
	}
	
	public boolean isEmpty() {
		return heapsize<=0;
	}
}
