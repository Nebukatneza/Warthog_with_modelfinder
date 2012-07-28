package de.stzoit.prover.cnf;

import java.util.HashSet;
import java.util.Set;

import de.stzoit.prover.collections.nativeType.IntVec;

public class Clause {
	private CNFSolver solver; /* solver that holds the clause */
	private IntVec lits;                    /* hold lits, invariant: lits[0] is first watched literal, 
	                                           lits[1] is second watched literal */
	private boolean tautology=false;
	protected long id;                      /* clause id, negative for deduced clauses, positive for 
	                                           original clauses */
	private String clauseName=null;         /* clause name */

	public Clause(CNFSolver sol) {
		solver=sol;
		lits=new IntVec();
	}
	
	public Clause(CNFSolver sol, long id) {
		this(sol);
		this.id=id;
	}
	
	public String getClauseName() {
		return clauseName;
	}

	public void setClauseName(String clauseName) {
		this.clauseName = clauseName;
	}
	
	/* numeric clause ID */
	public long getId() {
		return id;
	}
	
	public void push(String name) {
		if (name==null)
			return;
		
		String vname=name;
		int vnum=-1;
		boolean sign=true;
		if (name.startsWith("-")) {
			sign=false;
			vname=name.substring(1);
		}
		if (!solver.varExists(vname))
			vnum=solver.newVariable(vname);
		else
			vnum=solver.getVariable(vname);
		
		push(solver.var2lit(vnum, sign));
	}
	
	public void push(int lit) {
		if (lits.contains(lit))
			return;
		if (lits.contains(solver.oppositeLit(lit)))
			tautology=true;

		lits.push(lit);
	}
	
	public int get(int i) {
		return lits.get(i);
	}
	
	public boolean isLearnt() { /* override for learnt clauses as opposed to original clauses */
		return false;
	}
	
	public boolean isTautology() {
		return tautology;
	}
	
	public int size() {
		return lits.size();
	}
	
	public boolean sat() {
		for (int i=0; i<lits.size(); i++)
			if (solver.lit2val(lits.get(i))==CNFSolver.Val.TRUE)
				return true;
		return false;
	}
	
	/* returns true if all literals in clause have been assigned opposite values on level 0 */
	public boolean unsat() {
		for (int i=0; i<lits.size(); i++) {
			int lit=lits.get(i);
			if (solver.lit2val(lit)!=CNFSolver.Val.FALSE || solver.getLevel(lit)!=0)
				return false;
		}
		return true;
	}
	
	/* 
	 * try to move watch, if that fails assign other watch
	 * 
	 * return values: -1 assignment failed, 0 watch not moved, 1 watch moved
	 */
	public int moveWatch(int lit, int wl_ind) {
		/* lit has been assigned false, try to move it */
		int litpos=(lits.get(0)==lit) ? 0 : (lits.get(1)==lit ? 1 : 2147483647);
		int otherwatch=lits.get(1-litpos);
		
		/* clause satisfied, don't move */
		if (solver.lit2val(otherwatch)==CNFSolver.Val.TRUE)
			return 0;
		
		for (int i=2; i<lits.size(); i++) {
			CNFSolver.Val litval=solver.lit2val(lits.get(i));
			
			if (litval==CNFSolver.Val.TRUE || litval==CNFSolver.Val.UNKNOWN) {
				/* 
				 * 1. remove clause from lit's watchlist
				 * 2. swap lits(i) and lits(litpos)
				 * 3. add clause to lits(litpos)'s watchlist 
				 */
				solver.removeFromWatchlist(solver.oppositeLit(lit), wl_ind);
				swap(litpos, i);
				solver.addToWatchlist(solver.oppositeLit(lits.get(litpos)), this);
				
				return 1;
			}
		}
		/* watch couldn't be moved, propagate otherwatch; the propagated literal is always at position 0 */
		swap(0, 1-litpos);
		/* perform something like assign(sign(otherwatch), reason(this)), at this point a conflict might occur */
		return solver.assign(otherwatch, this) ? 0 : -1;
	}
	
	public int maxDecisionLevel() {
		return maxDecisionLevelExcept(-1);
	}
	
	public int maxDecisionLevelExcept(int lit) {
		int max=-1;
		for (int i=0; i<lits.size(); i++) {
			int _lit=lits.get(i);
			int level=solver.getLevel(_lit);
			if (_lit!=lit && level>max)
				max=level;
		}
		return max;
	}
	
	/* 
	 * upper 32 bits of result: largest decision level in clause, lower 32 bits: second largest decision level;
	 * postcondition: after both_largest_dls() literal with maximum dl is at position 0, literal with second 
	 *                largest dl (if any) is at position 1, if clause contains at least two unassigned literals,
	 *                those are placed at positions 0, 1 and (-1,-1) is returned
	 */
	/* 
	 * Postcondition:
	 *    i)   All literals set: pos0: literal with highest level, pos1: literal with l(pos_i)<=l(pos_1)<=l(pos0) 
	 *         for all i>=2
	 *    ii)  Exactly one literal UNKNOWN: pos0: literal with highest level, pos1: literal with UNKNOWN value
	 *    iii) At least two literals UNKNOWN: pos0: first unknown found, pos1: second unknown literal found
	 *    
	 * => if clause is not satisfied (no literal evaluates to true), the following remarks hold:
	 */
	public long bothLargestDecisionLevels() {
		long max=-1,
		     snd=-1;
		int  maxpos=-1, 
		     sndpos=-1;
		int  unknown_cnt=0,
		     unknown_pos0=-1,
		     unknown_pos1=-1;
		
		for (int i=0; i<lits.size(); i++) {
			int level=solver.getLevel(lits.get(i));
			if (level==-1) {
				unknown_cnt++;
				if (unknown_cnt==1)
					unknown_pos0=i;
				else if (unknown_cnt==2) {
					unknown_pos1=i;
					break;
				}
			}
			
			if (level>max) {
				snd=max;
				sndpos=maxpos;
				max=level;
				maxpos=i;
			} else if (level>snd) {
				snd=level;
				sndpos=i;
			}
		}
		
		if (unknown_cnt>=2) {
			swap(0, unknown_pos0);
			swap(1, (unknown_pos1==0 ? unknown_pos0 : unknown_pos1));
			return (-1L);
		} else if (unknown_cnt==1) {
			swap(1, unknown_pos0);
			sndpos=(sndpos==1 ? unknown_pos0 : sndpos);
			maxpos=(maxpos==1 ? unknown_pos0 : maxpos);
		}
		
		/* swap if possible */
		if (max>=0) {
			swap(0, maxpos);
			sndpos=(sndpos==0 ? maxpos : sndpos);
		}
		if (snd>=0 && unknown_cnt==0)
			swap(1, sndpos);
		
		/* pack */
		max<<=32;
		max|=((unknown_cnt==0 ? snd : (-1L))&0xffffffffL);
		
		return max;
	}
	
	public int unpackHigher(long i) {
		return (int)(i>>>32);
	}
	
	public int unpackLower(long i) {
		return (int)(i&0xffffffffL);
	}
	
	public void swap(int pos0, int pos1) {
		if (pos0!=pos1 && pos0<lits.size() && pos1<lits.size()) {
			int tmp=lits.get(pos0);
			lits.set(pos0, lits.get(pos1));
			lits.set(pos1, tmp);
		}
	}
	
	public String toString() {
		return toDimacsString()+" ("+toNamedString()+")";
	}
	
	public String toNamedString() {
		StringBuffer sb=new StringBuffer();
		for (int i=0; i<lits.size(); i++) {
			int lit=lits.get(i);
			sb.append((CNFSolver.sign(lit) ? "" : "-")+solver.lit2variable(lit)+" ");
		}
		return sb.toString();
	}
	
	public String toDimacsString() {
		StringBuffer sb=new StringBuffer();
		
		for (int i=0; i<lits.size(); i++)
			sb.append(CNFSolver.toDimacsLit(lits.get(i))+" ");

		sb.append("0");
		
		return sb.toString();
	}
	
	public void incJwh() {
		for (int i=0; i<lits.size(); i++) {
			int lit=lits.get(i);
			Variable var=solver.lit2variable(lit);
			if (var!=null) {
				/* jwh := sum 1^{-|C|} */
				var.setJwh(var.getJwh()+(1L<<((CNFSolver.sign(lit) ? 0 : 32)+(32-size()%32))));
				var.setPhase((var.getJwh()>>>32)<(var.getJwh()&0x00000000ffffffffL));
			}
		}
	}
	
	public Set<String> toSet() {
		Set<String> clause = new HashSet<String>();
		
		for (int i=0; i<lits.size(); i++) {
			clause.add(CNFSolver.toDimacsLit(lits.get(i)));
		}
		return clause;
	}
}
