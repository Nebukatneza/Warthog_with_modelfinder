package de.stzoit.prover.cnf.tracing;

import java.util.HashSet;
import java.util.Set;
import java.util.Stack;

import de.stzoit.prover.collections.ComparableWithIndex;
import de.stzoit.prover.collections.nativeType.LongVec;

public class DeductionInformation implements ComparableWithIndex<DeductionInformation> {
	private long id;
	protected long refCounter=0L;
	private LongVec parents;
	private ProofTracing solver;
	private boolean dirty=false;
	private int hind=-1;
	
	public DeductionInformation(ProofTracing solver, long id) {
		this.id=id;
		this.solver=solver;
		parents=new LongVec();
	}
	
	public long getId() {
		return id;
	}
	
	/* 
	 * If a clause is delete but its deduction information can't be deleted 
	 * (as it other clauses have been derived from it), it is marked dirty.
	 * As soon as the reference counter of dirty DeductionInformation reaches
	 * 0, it may be deleted as all clauses that once were derived from it have
	 * been deleted.
	 */
	void setDirty() {
		dirty=true;
	}
	
	boolean isDirty() {
		return dirty;
	}
	
	void clearDirty() {
		dirty=false;
	}
	
	/* add parent */
	public void addParent(long id) {
		parents.push(id);
		
		/* increment reference counter of newly added parent clause */
		if (solver.isDeduced(id))
			solver.getDeductionInformation(id).ref();
	}
	
	/* increase reference counter */
	public void ref() {
		refCounter++;
	}
	
	/* decrease reference counter */
	public void deref() {
		refCounter--;
	}
	
	/* 
	 * if a clause didn't take part in the deduction of other clauses, its
	 * DeductionInformation is deleteable 
	 */
	public boolean isDeletable() {
		return refCounter<=0L;
	}
	
	public void delete() {
		if (isDeletable()) {
			/* decrease reference counters of parents */
			for (int i=0; i<parents.size(); i++) {
				long parent=parents.get(i);
				if (solver.isDeduced(parent))
					solver.getDeductionInformation(parent).deref();
			}
			/* delete this from ProofTrace */
			solver.deleteDeductionInformation(id);
		} else {
			setDirty();
			solver.enqueueDirty(this);
		}
	}
	
	/* 
	 * get set of original clauses, i.e., if deduction information contains the
	 * parents of the empty clause, this should generate a unsatisfiable core 
	 * for the formula under consideration 
	 */
	public Set<Long> getOriginalClauses() {
		Stack<Long> todo=new Stack<Long>();
		Set<Long> result=new HashSet<Long>();
		
		fillStackOriginal(todo, result);
		while (!todo.isEmpty()) {
			DeductionInformation parentClause=solver.getDeductionInformation(todo.pop());
			parentClause.fillStackOriginal(todo, result);
		}
		
		return result;
	}
	
	/* 
	 * Side effect: Fill worker stack with parents which are deduced, add original
	 *              clauses to result 
	 */
	protected void fillStackOriginal(Stack<Long> todo, Set<Long> result) {
		for (int i=0; i<parents.size(); i++) {
			long clauseId=parents.get(i);
			
			if (solver.isDeduced(clauseId)) /* -> parent is deduced clause */
				todo.add(clauseId);
			else
				result.add(clauseId);
		}
	}
	
	/*
	 * Get IDs of DeductionInformation which took part in the deduction of this 
	 * clause/DeductionInformation
	 */
	public Set<Long> getDerivationalClauses() {
		Stack<Long> todo=new Stack<Long>();
		Set<Long> result=new HashSet<Long>();
		
		fillStackDeduced(todo, result);
		while (!todo.isEmpty()) {
			DeductionInformation parentClause=solver.getDeductionInformation(todo.pop());
			parentClause.fillStackDeduced(todo, result);
		}
		
		return result;
	}
	
	/*
	 * Side effect: Fill worker stack with parents which are deduced, add deduced
	 *              clauses to result
	 */
	protected void fillStackDeduced(Stack<Long> todo, Set<Long> result) {
		for (int i=0; i<parents.size(); i++) {
			long clauseId=parents.get(i);
			
			if (solver.isDeduced(clauseId)) {/* -> parent is deduced clause */
				todo.add(clauseId);
				result.add(clauseId);
			}
		}
	}

	/* this > that iff this.refCounter < that.refCounter */
	public int compareTo(DeductionInformation that) {
		return -((refCounter-that.refCounter < 0L) 
				  ? -1 
				  : (refCounter==that.refCounter ? 0 : 1));
	}

	public int index() {
		return hind;
	}
	
	public void setIndex(int i) {
		hind=i;
	}
	
	/* return string representation of clause ancestry */
	public String toString() {
		StringBuilder sb=new StringBuilder(id+": ");
		
		for (int i=0; i<parents.size(); i++)
			sb.append(" "+parents.get(i));
		
		return sb.toString();
	}
	
	public Set<String> getClause(long id) {
		return solver.isDeduced(id) ? solver.getDeductionInformation(id).toClause() 
		                            : solver.id2original.get(id).toClause();
	}
	
	private String getNegation(String lit) {
		return lit.startsWith("-") ? lit.substring(1) : "-"+lit;
	}
	
	private String findResolutionLiteral(Set<String> left, Set<String> right) {
		for (String lit : right)
			if (left.contains(getNegation(lit)))
				return lit;
		return null;
	}
	
	private Set<String> resolve(Set<String> left, Set<String> right) {
		if (left==null || left.isEmpty())
			return right;
		else {
			String lit=findResolutionLiteral(left, right);
			left.remove(getNegation(lit));
			right.remove(lit);
			left.addAll(right);
			
			return left;
		}
	}
	
	public Set<String> toClause() {
		Set<String> clause = new HashSet<String>();
		
		for (int i=0; i<parents.size(); i++)
			clause = resolve(clause, getClause(parents.get(i)));
		
		return clause;
	}
	
	public static long toTraceCheckId(ProofTracing solver, long id) {
		if (id == 0) /* special handling for empty clause */
			return 1;
		else
			return solver.isDeduced(id) ? (-id)*2 : id*2+1;
	}
	
	public String toTraceCheckEntry() {
		Set<String> clause = toClause();
		
		StringBuilder sb = new StringBuilder();
		
		sb.append(toTraceCheckId(solver, id)+" ");
		for (String lit : clause)
			sb.append(lit+" ");
		
		sb.append("0 ");
		for (int i=0; i<parents.size(); i++)
			sb.append(toTraceCheckId(solver, parents.get(i))+" ");
		
		sb.append("0");
		
		return sb.toString();
	}
}
