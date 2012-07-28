package de.stzoit.prover.cnf;

public class LearntClause extends Clause {
	private int activity=0;
	private int references=0;
	
	public LearntClause(CNFSolver sol) {
		super(sol);
	}
	
	public LearntClause(CNFSolver sol, long id) {
		super(sol, id);
	}
	
	public boolean isLearnt() {
		return true;
	}
	
	/* we must not delete clauses that are locked */
	public boolean is_locked() {
		return references>0;
	}
	
	/* when clause is attached as reason, the reference counter is increased */
	public void ref() {
		references++;
	}
	
	/* when a clause is detached (a variable is reset to UNKNOWN), the reference counter is decreased */
	public void deref() {
		references--;
	}
	
	public void increaseActivity() {
		activity++;
	}
	
	/* 
	 * called after clause removal by compactify(), intended effect: make clauses not invovled in recent conflicts 
	 * more likely to be removed during the next elimination round
	 */
	public void decreaseActivity() {
		activity/=2;
	}
	
	public void setActivity(int a) {
		activity=a;
	}
	
	public int getActivity() {
		return activity;
	}
}
