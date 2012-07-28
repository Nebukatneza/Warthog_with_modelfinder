package de.stzoit.prover.cnf.tracing;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.stzoit.prover.cnf.CNFSolver;
import de.stzoit.prover.cnf.Clause;
import de.stzoit.prover.cnf.LearntClause;
import de.stzoit.prover.cnf.Variable;
import de.stzoit.prover.collections.HeapWithIndex;
import de.stzoit.prover.collections.IVec;
import de.stzoit.prover.collections.Vec;
import de.stzoit.prover.collections.nativeType.IntVec;


/*
 * INVARIANTS:
 * 
 *   1. Binary and unit clauses are never deleted
 *   
 *   2. Binary and unit clauses are never added redundantly (i.e., if e.g. [1, -2] is already present in the 
 *      solver, addition of [-2, 1] will not add any new clauses); requires modification of addClause (not 
 *      allowing binary or unit clauses to be added more than once doesn't violate any constraints because of 
 *      invariant 1)
 *   3. If a literal L is propagated by a binary clause, i.e. the reason is R, the binary clause that 
 *      propagated L is L/-R
 */
public class ProofTracing extends CNFSolver {
	private HashMap<String,Long> unaryBinaryId=null;         /* Mapping {unit,binary} clause -> clauseID      */
	private HashMap<Long,DeductionInformation> deduced=null; /* Mapping clause IDs -> deduction information   */
	private HashMap<Long,String> unaryBinaryName=null;       /* Names for unit and binary clauses             */
	protected HashMap<Long,ClausePointer> id2original=null;  /* Mapping clause IDs to clause (1-, 2-, n-ary)  */
	private long originalid=1L;                              /* top-most original clause id                   */
	private long deducedid=-1L;                              /* top-most deduced clause id                    */
	private DeductionInformation emptyClause=null;           /* empty clause derivation (if solver is in 
																state UNSAT and emptyClause=null, [] has been
																added to the solver)                          */
	private HeapWithIndex<DeductionInformation> dustBin=null;/* holds ids of dirty clauses (deletion 
	                                                            candidates)                                   */
	private static final int MARK_SAT_STATUS=0;              /* index of satisfiability status in mark        */
	private static final int MARK_ORIG_CLAUSE_COUNT=1;       /* number of original clauses at marking level   */
	private static final int MARK_VARIABLE_COUNT=2;          /* number of variables at marking level          */
	private static final int MARK_WATCHLIST_LENGTH=3;        /* watchlist lenght at marking level             */
	private static final int MARK_LEARNT_CLAUSE_COUNT=4;     /* number of learnt clauses at marking level     */
	private static final int MARK_UNIT_LIST_LENGTH=5;        /* length of unit clause list at marking level   */
	private static final int MARK_MAX_ORIG_CLAUSE_ID=6;      /* max. original clause id (next orig. ID)       */
	private static final int MARK_MIN_LEARNT_CLAUSE_ID=7;    /* min. learnt clause id (next learnt ID)        */
	private static final int MARK_BINARY_CLAUSE_START=8;     /* start of bounds list for binary watchlists    */
	protected IVec<Long[]> marks;                            /* marks for {in,de}cremental SAT solving        */
	
	private enum ClauseType {
		UNIT, BINARY, NARY
	}
	
	class ClausePointer {
		private ClauseType type;
		private int lit0, lit1;
		private Clause nary;
		private long id;
		private String name;
		
		public ClausePointer(int lit) {
			lit0=lit;
			type=ClauseType.UNIT;
			id=unaryBinaryId.get(genId(lit));
			name=unaryBinaryName.get(id);
		}
		
		public ClausePointer(int lit0, int lit1) {
			this.lit0=lit0;
			this.lit1=lit1;
			type=ClauseType.BINARY;
			id=unaryBinaryId.get(genId(lit0, lit1));
			name=unaryBinaryName.get(id);
		}
		
		public ClausePointer(Clause clause) {
			nary=clause;
			type=ClauseType.NARY;
			id=clause.getId();
			name=clause.getClauseName();
		}
		
		private String literal2string(int lit) {
			Variable var=lit2variable(lit);
			return (sign(lit) ? "" : "-")+var.toString();
		}
		
		public String toString() {
			switch (type) {
				case UNIT:
					return id+": "+name+": "+literal2string(lit0);
				case BINARY:
					return id+": "+name+": "+literal2string(lit0)+"" +" "+literal2string(lit1);
				default:
					return id+": "+name+": "+nary.toNamedString();
			}
		}
		
		public Set<String> toClause() {
			Set<String> clause = new HashSet<String>();
			
			switch (type) {
				case UNIT:
					clause.add(CNFSolver.toDimacsLit(lit0));
					break;
				case BINARY:
					clause.add(CNFSolver.toDimacsLit(lit0));
					clause.add(CNFSolver.toDimacsLit(lit1));
					break;
				default:
					clause = nary.toSet();
					break;
					
			}
			return clause;
		}
		
		public String toTraceCheckEntry(ProofTracing solver) {
			switch (type) {
				case UNIT:
					return DeductionInformation.toTraceCheckId(solver, id)+" "+CNFSolver.toDimacsLit(lit0)+" 0 0";
				case BINARY:
					return DeductionInformation.toTraceCheckId(solver, id)+" "+CNFSolver.toDimacsLit(lit0)+" "+CNFSolver.toDimacsLit(lit1)+" 0 0";
				default:
					return DeductionInformation.toTraceCheckId(solver, id)+" "+nary.toDimacsString()+" 0";
			}
		}
	}
	
	public ProofTracing() {
		this("ProofTracing");
	}
	
	public ProofTracing(String name) {
		super(name);
		unaryBinaryId  =new HashMap<String,Long>();
		deduced        =new HashMap<Long,DeductionInformation>();
		unaryBinaryName=new HashMap<Long,String>();
		marks          =new Vec<Long[]>();
		id2original    =new HashMap<Long,ClausePointer>();
		dustBin        =new HeapWithIndex<DeductionInformation>();
		
		/* 
		 * conservative choice: don't perform clause deletion when proof 
		 * tracing is activated 
		 */
		perform_clause_deletion=false;
	}
	
	/* set back clause IDs to an initial value */
	private void resetClauseIds() {
		if (unaryBinaryId!=null)
			unaryBinaryId.clear();
		originalid=1L;
		deducedid=-1L;
	}
	
	public boolean isDeduced(long id) {
		return id<0L;
	}
	
	private long getClauseId(String id) {
		Long rv=unaryBinaryId.get(id);
		if (rv==null)
			return 0L;
		return rv;
	}
	
	/* retrieve ID for a unit clause */
	long getClauseId(int lit) {
		return getClauseId(genId(lit));
	}
	
	/* retrieve ID for a binary clause */
	long getClauseId(int lit0, int lit1) {
		return getClauseId(genId(lit0, lit1));
	}
	
	/* generate a unique ID for a unit clause */
	private String genId(int lit) {
		return "U"+lit;
	}
	
	/* generate a unique ID for a binary clause */
	private String genId(int lit0, int lit1) {
		if (lit0<lit1)
			return "B"+lit0+","+lit1;
		else
			return "B"+lit1+","+lit0;
	}
	
	/* return a new unique ID for a deduced clause */
	protected long getNewDeducedId() {
		return this.deducedid--;
	}
	
	/* return a new unique ID for a original clause */
	public long getNewOriginalId() {
		return this.originalid++;
	}
	
	/* add the ancestry information for a deduced clause with ID id */
	protected void addDeductionInformation(long id, DeductionInformation clause) {
		deduced.put(id, clause);
	}
	
	public void deleteDeductionInformation(long id) {
		deduced.remove(id);
		/* ATTENTION: unary and binary deduced clauses will never be deleted unless via undo() */
	}
	
	/* add a binary clause to ID database */
	protected void addBinaryId(int lit0, int lit1, long id) {
		unaryBinaryId.put(genId(lit0, lit1), id);
	}
	
	/* add a name for a binary clause */
	protected void addBinaryName(long id, String clauseName) {
		unaryBinaryName.put(id, clauseName);
	}
	
	/* add a unit clause to ID database */
	protected void addUnaryId(int lit, long id) {
		unaryBinaryId.put(genId(lit), id);
	}
	
	/* add a name for a unit clause */
	protected void addUnaryName(long id, String clauseName) {
		unaryBinaryName.put(id, clauseName);
	}
	
	/* get deduction information for deduced clause with ID id or null */
	DeductionInformation getDeductionInformation(long id) {
		return deduced.get(id);
	}
	
	/* enqueue a clause in the dirty queue */
	void enqueueDirty(DeductionInformation clause) {
		if (isDeduced(clause.getId()))
			dustBin.quickInsert(clause);
	}
	
	/* delete dirty elements with refCounter==0 */
	void weedOutDirty() {
		while (!dustBin.isEmpty() && dustBin.peek().isDeletable()) {
			DeductionInformation clause=dustBin.heapExtractMax();
			clause.delete();
		}
	}
	
	public boolean pushClause(Clause clause) throws Exception {
		return pushClause(clause, "none");
	}
	
	public boolean pushClause(Clause clause, String clauseName) throws Exception {
		/* 
		 * adjusted addClause for proof tracing; intended use of 'name' 
		 * parameter: associate clauses with position in non-cnf formula, 
		 * this should enable really rapid retrieval of skeletonized 
		 * explanations 
		 */
		
		/* check clause */
		if (clause.isTautology()) {
			return true;
		}
		
		if (!clause.isLearnt())
			backtrack(0, true);
		
		if (clause.size()==0) {
			/* empty clause was added -> no derivation */
			emptyClause=new DeductionInformation(this, 0L);
			state=State.UNSAT;
		}
		else if (clause.size()==1) {
			if (state!=State.UNSAT && level>0) /* backtrack to a) Level 0, b) Level beneath get_level(cls[0]) */
				backtrack(0, true);
			
			if (getClauseId(clause.get(0))==0L) {
				unitfacts.push(clause.get(0));
				addUnaryId(clause.get(0), clause.getId());
				addUnaryName(clause.getId(), clauseName);
			}

			if (clause.isLearnt())
				stats.statLearnUnit();
			else
				id2original.put(clause.getId(), new ClausePointer(clause.get(0)));
			
			if (state!=State.UNSAT && !assign(clause.get(0), null)) {/* do not perform assign if state==UNSAT */
				/* compute empty clause derivation */
				collectEmptyClauseDerivation();
				state=State.UNSAT;
			}
		}
		else {
			if (state!=State.UNSAT && !clause.sat() && !clause.isLearnt()) {
				backtrack(0, true);
				long packed=clause.bothLargestDecisionLevels();
				
				if (packed==0L) { /* all literals failed and assigned at level 0 */
					state=State.UNSAT;
					return false;
				}
				else if (clause.unpackHigher(packed)==-1 && clause.unpackLower(packed)==-1) /* >= 2 literals unassigned */
					/* do nothing */;
				else if (clause.unpackLower(packed)==-1) {
					if (clause.unpackHigher(packed)==0) /* propagate */
					{
						if (!assign(clause.get(1), (clause.size()>2 ? clause : oppositeLit(clause.get(0))))) {
							/* compute empty clause derivation */
							collectEmptyClauseDerivation();
							state=State.UNSAT;
							return false;
						}							
					} 
					else{
						backtrack(Math.max(0, clause.unpackHigher(packed)-1), true);
					}
				}
				else {
					backtrack(Math.max(0, clause.unpackLower(packed)-1), true);
				}
			} else if (state!=State.UNSAT && !clause.sat() && clause.isLearnt()) {
				/* 
				 *      by convention, learnt clauses of length >= 2 include the asserted literal at position 0
				 *      and a literal assigned at the highest decision level beneath the assertion level at 
				 *      position 1.
				 */
				backtrack(Math.max(0, getLevel(clause.get(1))));
			}
			
			if (clause.size()==2 && getClauseId(clause.get(0), clause.get(1))==0L) { /* new binary clauses */
				addBinaryId(clause.get(0), clause.get(1), clause.getId());
				addBinaryName(clause.getId(), clauseName);
				
				IntVec bwl0=binwatchlists.get(oppositeLit(clause.get(0)));
				IntVec bwl1=binwatchlists.get(oppositeLit(clause.get(1)));
				
				bwl0.push(clause.get(1));
				bwl1.push(clause.get(0));
				
				if (clause.isLearnt())
					stats.statLearnBin();
				else
					id2original.put(clause.getId(), new ClausePointer(clause.get(0), clause.get(1)));
			} else if (clause.size()>2) { /* >2 */
				clause.setClauseName(clauseName);
				
				IVec<Clause> wl0=watchlists.get(oppositeLit(clause.get(0)));
				IVec<Clause> wl1=watchlists.get(oppositeLit(clause.get(1)));
				
				wl0.push(clause);
				wl1.push(clause);
				
				if (clause.isLearnt()) {
					stats.statLearn();
					learntclauses.push((LearntClause) clause);
				}
				else {
					origclauses.push(clause);
					id2original.put(clause.getId(), new ClausePointer(clause));
				}
			}
		}
		if (initial_phase==2 && level==0 && state!=State.UNSAT)
			clause.incJwh();
		
		/* after adding a clause, the solver state is at least UNKNOWN if not UNSAT */
		if (state!=State.UNSAT)
			state=State.UNKNOWN;
		
		return state!=State.UNSAT;
	}

	public void handleConflict() throws Exception {
		/*
		 * adjust handle_conflict() to record a derivation for each 
		 * deduced/learnt clause
		 */
		LearntClause learnt=new LearntClause(this, getNewDeducedId());
		int i=trail.size()-1,
		    n=0,
		    lit=0;
		Object reason=conflict_reason;
		DeductionInformation derivation=new DeductionInformation(this, learnt.getId());
		
		do {
			if (reason==null) /* decision */
				break;
			if (reason instanceof Integer) {/* binary clause */
				if (lit==0 && !seen.get(lit2var(conflict_lit))) {
					seen.set(lit2var(conflict_lit), true);
					if (level<=getLevel(conflict_lit))
						n++;
					else { /* may not happen... */
						learnt.push(conflict_lit);
					}
				}
				if (!seen.get(lit2var((Integer)reason))) {
					seen.set(lit2var((Integer)reason), true);
					if (level<=getLevel((Integer)reason))
						n++;
					else {
						learnt.push(oppositeLit((Integer)reason));
					}
				}
				
				/* record participation in derivation */
				derivation.addParent(getClauseId(lit==0 ? conflict_lit : lit, oppositeLit((Integer) reason)));
			} else {
				Clause cls=(Clause)reason;
				for (int j=(lit==0 ? 0 : 1); j<cls.size(); j++) {
					/* 
					 * UIP is reached, if all but one literals of the current level are resolved, i.e. if a 
					 * literal at or above the current level is encountered, increase counter, else push it to
					 * the learnt clause
					 */
					int _lit=cls.get(j);
					if (!seen.get(lit2var(_lit))) {
						seen.set(lit2var(_lit), true);
						if (level<=getLevel(_lit))
							n++;
						else {
							learnt.push(_lit);
						}
					}
					if (!glucose_clause_scores && cls.isLearnt())
						((LearntClause)cls).increaseActivity();
				}
				
				/* record participation in derivation */
				derivation.addParent(cls.getId());
			}
			/* 
			 * jump to last assigned literal on trail which contributes to conflict 
			 * (i.e. takes part in conflict clause resolution)
			 */
			while (!seen.get(lit2var(trail.get(i--))))
				;
			lit=trail.get(i+1);
			seen.set(lit2var(lit), false);
			reason=lit2variable(lit).reason();
			n--; /* literal is resolved, thus decrease counter */
		} while (n > 0);
		learnt.push(oppositeLit(lit));
		learnt.swap(0, learnt.size()-1); /* uip at position 0 */
		
		/* put literal with second largest decision level at position 1 */
		int snd_pos=1;
		int bt_level;
		permdiff_curr++;
		int lbd=1;
		for (i=1; i<learnt.size(); i++) {
			int __lit=learnt.get(i);
			int _level=getLevel(__lit);
			
			if (_level>getLevel(learnt.get(snd_pos)))
				snd_pos=i;
			if (glucose_clause_scores && perm_diff.get(_level)!=permdiff_curr) {
				perm_diff.set(_level, permdiff_curr);
				lbd++;
			}
			
			seen.set(lit2var(__lit), false);
			lit2variable(__lit).incScore();
		}
		if (glucose_clause_scores) /* set glucose-style clause activity */
			learnt.setActivity(lbd);
		
		seen.set(lit2var(learnt.get(0)), false);
		lit2variable(learnt.get(0)).incScore();
		learnt.swap(1, snd_pos);
		bt_level=(learnt.size()<=1 ? 0 : getLevel(learnt.get(1)));
		
		/* add clause, backtrack, propagate uip, restart if threshold is met */
		stats.statConflict();
		boolean do_restart=stats.statPerformRestart();
		
		if (do_restart) { /* backtrack to level 0, reset counter */
			backtrack(0);
			stats.statRestart();
		}
		
		/* save derivation information for learnt clause */
		addDeductionInformation(derivation.getId(), derivation);
		
		/* ATTENTION HERE: might return false (e.g. unit deduced but unit already set => UNSAT) */
		pushClause(learnt);
		/* don't assign uip if restart was performed and the asserting level of the learnt clause is >0 */
		if (learnt.size()>1 && (!do_restart||bt_level==0)) {
			assign(learnt.get(0), (learnt.size()==2 ? oppositeLit(learnt.get(1)) : learnt));
		}
	}
	
	public boolean sat() throws Exception {
		/*
		 * adjust sat() to record level 0 derivation after detecting
		 * unsatisfiability
		 */
		/* initialize max. learnt clause db size */
		stats.statSetMaxLearnt(origclauses.size());

		if (state==State.UNSAT) {
			return false;
		}
		else {
			while (true) {
				if (!bcp()) {
					if (level==0) {
						/* compute empty clause derivation */
						collectEmptyClauseDerivation();
						state=State.UNSAT;
						return false;
					}
					handleConflict();

					if (state==State.UNSAT) 
						;
				} else {
					/* reduce db */
					if (perform_clause_deletion && learntclauses.size()-trail.size() > stats.statGetMaxLearnt())
						weedOutLearnt();
					
					/* perform decision */
					if (!decide()) {
						state=State.SAT;
						return true;
					}
				}
			}
		}
	}
	
	public void weedOutLearnt() {
		/*
		 * adjusted learnt clause deletion to try to delete clauses if 
		 * possible and to flag clause ancestry information whose 
		 * associated clause is deleted but which can't be deleted 
		 * itself as dirty; after deleting learnt clauses, check if 
		 * ancestry information marked dirty can now be deleted
		 */
		LearntClause[] l=learntclauses.toArray(new LearntClause[0]);
		Arrays.sort(l, new Comparator<LearntClause>() {
			public int compare(LearntClause o1,
					LearntClause o2) {
				if (o1==null || o2==null) {
					if (o1==null && o2==null)
						return 0;
					else if (o1==null)
						return -1;
					else
						return 1;
				}
				return o1.getActivity()-o2.getActivity();
			}
		});
		
		int deleted=0;
		if (glucose_clause_scores)
			for (int i=l.length-1; i>=0 && deleted<=l.length/2; i--) {
				if (l[i]!=null && !l[i].is_locked()) { /* delete clause */
					/* try to delete deduction information for learnt clause */
					getDeductionInformation(l[i].getId()).delete();
					
					detachClause(l[i]);
					learntclauses.set(learntclauses.indexOf(l[i]), null);
					deleted++;
				}
			}
		else
			for (int i=0; i<l.length && deleted<=l.length/2; i++) {
				if (l[i]!=null && !l[i].is_locked()) { /* delete clause */
					/* try to delete deduction information for learnt clause */
					getDeductionInformation(l[i].getId()).delete();
					
					detachClause(l[i]);
					learntclauses.set(learntclauses.indexOf(l[i]), null);
					deleted++;
				}
			}
		if (deleted>0) {
			/* try to reduce dirty deduction information */
			weedOutDirty();
			
			compactify();
			System.gc(); /* perform garbage collection */
		}
	}
	
	/*
	 * Marking information:
	 * 
	 * +--------+------+------+---------+---------+-------+--------------+----------------+-----------+
	 * | status | orig | vars | w-lists | learnts | units | max. orig ID | min. learnt ID | binary... |
	 * +--------+------+------+---------+---------+-------+--------------+----------------+-----------+
	 * 
	 * status:         satisfiability status (-1: UNSAT, 0: UNKNOWN, 1: SAT)
	 * orig:           clauses of length >2 at time of marking (stack bound)
	 * vars:           variables at time of marking (stack bound)
	 * w-lists:        watchlists (stack bound)
	 * learnts:        learnt clauses at time of marking (stack bound)
	 * units:          unit clauses at time of marking (stack bound)
	 * max. orig ID:   maximum ID for original clauses (i.e. next ID assigned to a new original clause)
	 * min. learnt ID: maximum ID for learnt clauses (i.e., next ID assigned to a new learnt clause)
	 * binary:         array of stack bounds for binary clauses (adjacency list lengths)
	 */
	public void pop() throws Exception {
		/*
		 * adjusted undo() to delete all ancestry information which doesn't 
		 * belong to the current level
		 */
		stats.statReset(); /* else number of decisions will produce timeout from one point in solving */
		if (marks.size()<=0) {
			return;
		}
		else if (marks.last().length<MARK_BINARY_CLAUSE_START) {
			throw new Exception("Mark supposed to contain more than 6 bounds");
		}
		else {
			Long mark[]=marks.last();
			int binlength=(int)(score_saving ? (mark.length-MARK_BINARY_CLAUSE_START-(mark[MARK_VARIABLE_COUNT]-1)) 
			                                 : mark.length-MARK_BINARY_CLAUSE_START);
			int shrinkTo=0;
			
			marks.pop();
			backtrack(-1); /* must be performed here, otherwise GC might have erased clauses before deref'ing */
			
			/* restore solver state */
			state=(mark[MARK_SAT_STATUS]<0 ? State.UNSAT : State.UNKNOWN);
			
			/* shrink clauses */
			shrinkTo=(int)Math.max(0, Math.min(origclauses.size(), mark[MARK_ORIG_CLAUSE_COUNT]));
			for (int i=origclauses.size()-1; i>=shrinkTo; i--) {
				Clause clause=origclauses.get(i);
				
				id2original.remove(clause.getId());
				detachClause(clause);
			}
			origclauses.shrinkTo(shrinkTo);
			
			/* reset next original clause id */
			originalid=mark[MARK_MAX_ORIG_CLAUSE_ID];
			
			/* shrink learnts */
			shrinkTo=(int)Math.max(0, Math.min(learntclauses.size(), mark[MARK_LEARNT_CLAUSE_COUNT]));
			for (int i=learntclauses.size()-1; i>=shrinkTo; i--) {
				/* try to delete deduction information associated with learnt clause */
				getDeductionInformation(learntclauses.get(i).getId()).delete();
				
				detachClause(learntclauses.get(i));
			}
			learntclauses.shrinkTo(shrinkTo);
			
			/* shrink variables */
			shrinkTo=(int)Math.max(0, Math.min(variables.size(), mark[MARK_VARIABLE_COUNT]));
			for (int i=shrinkTo; i<variables.size(); i++) {
				if (variables.get(i).getName()!=null) {
					name2var.remove(variables.get(i).getName());
				}
				if (variables.get(i).index()<0)
					;
				else
					;
				varq.delete(variables.get(i));
			}
			variables.shrinkTo(shrinkTo);
			
			/* shrink watchlists */
			watchlists.shrinkTo((int)Math.min(watchlists.size(), mark[MARK_WATCHLIST_LENGTH]));
			
			/* shrink units */
			int unitShrink=(int)Math.min(unitfacts.size(), mark[MARK_UNIT_LIST_LENGTH]);
			for (int i=unitfacts.size(); i>unitShrink; i--) {
				/* delete unit clause entries in unaryBinaryID and unaryBinaryName */
				int lit=unitfacts.get(i);
				long unitId=getClauseId(lit);
				
				if (isDeduced(unitId))
					getDeductionInformation(unitId).delete();
				else
					id2original.remove(unitId);
				
				unaryBinaryId.remove(genId(lit));
				unaryBinaryName.remove(unitId);
			}
			unitfacts.shrinkTo(unitShrink);
			
			/* shrink binary watchlists */
			binwatchlists.shrinkTo(Math.min(binwatchlists.size(), binlength));
			
			for (int i=MARK_BINARY_CLAUSE_START; i<mark.length; i++) {
				if (i-MARK_BINARY_CLAUSE_START >= binwatchlists.size())
					break;
				
				IntVec bwl=binwatchlists.get(i-MARK_BINARY_CLAUSE_START);
				if (bwl!=null && mark[i]>=0) {
					int binaryShrink=(int)Math.min(bwl.size(), mark[i]);
					for (int j=bwl.size(); j>binaryShrink; j--) {
						/* delete binary clause entries in unaryBinaryID and unaryBinaryName */
						int lit0=bwl.get(j), 
							lit1=oppositeLit(i-MARK_BINARY_CLAUSE_START);
						long binaryId=getClauseId(lit0, lit1);
						
						if (isDeduced(binaryId))
							getDeductionInformation(binaryId).delete();
						else
							id2original.remove(binaryId);
						
						if (binaryId!=0L) {
							unaryBinaryId.remove(genId(lit0, lit1));
							unaryBinaryName.remove(binaryId);
						}
					}
					bwl.shrinkTo(binaryShrink);
				}
			}
			
			/* 
			 * try to delete dirty flagged deduction information; at this point, 
			 * all the deduction information for all the clauses learnt at this 
			 * marking level should have been deleted
			 */
			weedOutDirty();
			assertDeductionInformationDeleted(mark[MARK_MIN_LEARNT_CLAUSE_ID]);
			
			if (state!=State.UNSAT) { /* assign unitfacts */
				for (int i=0; i<unitfacts.size(); i++)
					if (!assign(unitfacts.get(i), null)) {
						collectEmptyClauseDerivation();
						state=State.UNSAT;
						return;
					}
			}
			if (score_saving)
				resetScoresAndPhases(mark, MARK_BINARY_CLAUSE_START+binlength);
		}
	}
	
	private void assertDeductionInformationDeleted(long start) throws Exception {
		for (long id=start; id>deducedid; id--)
			if (getDeductionInformation(id)!=null) 
				/* deduction information has not been deleted though it should have been! */
				throw new Exception("DeductionInformation for learnt clause with ID "+id
						+" from forbidden range ["+start+", "+deducedid+"[ not deleted!");
	}
	
	public void reset() {
		backtrack(-1);           /* clear trail and reasons */
		stats.statReset();
		state=State.UNKNOWN;
		permdiff_curr=0;
		conflict_reason=null;
		
		/* clear clause structures */
		learntclauses.clear();   /* clear learnt clauses */
		unitfacts.clear();       /* clear unit clauses */
		origclauses.clear();     /* clear original clauses */
		
		/* clear structures for proof tracing */
		unaryBinaryId.clear();   /* clear {unary,binary} clause -> ID mapping */
		unaryBinaryName.clear(); /* clear {unary,binary} clause -> name mapping */
		deduced.clear();         /* clear clause id -> deduction information mapping */
		id2original.clear();     /* clear clause id -> output information mapping */
		emptyClause=null;        /* clear empty clause */
		dustBin.clear();         /* clear dirty deduction information queue */
		originalid=1L;           /* reset original clause ids */
		deducedid=-1L;           /* reset deduced clause ids */
		
		/* clear watchlists */
		watchlists.shrinkTo(2);
		binwatchlists.shrinkTo(2);
		
		variables.shrinkTo(1);   /* clear variables */
		levels.shrinkTo(1);      /* clear levels */
		varq.clear();            /* clear variable queue */
		seen.shrinkTo(1);        /* clear seen */
		perm_diff.shrinkTo(1);   /* clear perm_diff */
		name2var.clear();        /* clear name variable mapping */
		
		/* {in,de}cremental structures */
		marks.clear();           /* clear marks */
		
		/* suggest GC */
		System.gc();
		
		resetClauseIds();
	}
	
	/*
	 * Marking information:
	 * 
	 * +--------+------+------+---------+---------+-------+--------------+----------------+-----------+
	 * | status | orig | vars | w-lists | learnts | units | max. orig ID | min. learnt ID | binary... |
	 * +--------+------+------+---------+---------+-------+--------------+----------------+-----------+
	 * 
	 * status:         satisfiability status (-1: UNSAT, 0: UNKNOWN, 1: SAT)
	 * orig:           clauses of length >2 at time of marking (stack bound)
	 * vars:           variables at time of marking (stack bound)
	 * w-lists:        watchlists (stack bound)
	 * learnts:        learnt clauses at time of marking (stack bound)
	 * units:          unit clauses at time of marking (stack bound)
	 * max. orig ID:   maximum ID for original clauses (i.e. next ID assigned to a new original clause)
	 * min. learnt ID: maximum ID for learnt clauses (i.e., next ID assigned to a new learnt clause)
	 * binary:         array of stack bounds for binary clauses (adjacency list lengths)
	 */
	public void save() {
		Long mark[];
		if (!score_saving)
			mark=new Long[MARK_BINARY_CLAUSE_START+binwatchlists.size()];
		else
			mark=new Long[MARK_BINARY_CLAUSE_START+binwatchlists.size()+(variables.size()-1)];
		
		mark[MARK_SAT_STATUS]=(state==State.UNSAT ? -1L : (state==State.SAT ? 1L : 0L)); /* status */
		mark[MARK_ORIG_CLAUSE_COUNT]=(long) origclauses.size();
		mark[MARK_VARIABLE_COUNT]=(long) variables.size();
		mark[MARK_WATCHLIST_LENGTH]=(long) watchlists.size();
		mark[MARK_LEARNT_CLAUSE_COUNT]=(long) learntclauses.size();
		mark[MARK_UNIT_LIST_LENGTH]=(long) unitfacts.size();
		mark[MARK_MAX_ORIG_CLAUSE_ID]=originalid;
		mark[MARK_MIN_LEARNT_CLAUSE_ID]=deducedid;
		
		for (int i=0; i<binwatchlists.size(); i++) {
			if (binwatchlists.get(i)!=null) {
				mark[i+MARK_BINARY_CLAUSE_START]=(long) binwatchlists.get(i).size();
			}
			else {
				mark[i+MARK_BINARY_CLAUSE_START]=-1L;
			}
		}
		if (score_saving)
			saveScoresAndPhases(mark, MARK_BINARY_CLAUSE_START+binwatchlists.size());
		
		/* push marking on marks stack */
		marks.push(mark);
	}
	
	protected void saveScoresAndPhases(Long mark[], int offset) {
		if (mark.length < (offset+variables.size()-1))
			return;
		for (int i=1; i<variables.size(); i++) {
			Variable var = variables.get(i);
			mark[offset+(i-1)] = (long) ((var.getScore()<<1)|(var.getPhase() ? 0x1 : 0x0));
		}
	}
	
	protected void resetScoresAndPhases(Long mark[], int offset) {
		for (int i=offset; i<mark.length; i++) {
			int idx=(i-offset)+1;
			
			if (!(idx<variables.size()))
				break;
			
			Variable var = variables.get(idx);
			
			var.setScore((int) (mark[i]>>>1));
			var.setPhase(((mark[i]&0x1) > 0));
		}
		varq.restoreHeapProperty();
	}
	
	private void collectEmptyClauseDerivation() throws Exception {
		/* 
		 * traverse trace backward in order to collect the derivation of 
		 * the empty clause; not destroying the trail should be ok as 
		 * the solver state won't change before a undo() occurred which 
		 * will set it back entirely
		 */
		DeductionInformation derivation=new DeductionInformation(this, 0L);
		Object reason=conflict_reason;
		int lit=conflict_lit,
			trailPointer=trail.size()-1;

		exceptionalCondition(level>0, "Cannot compute empty clause at decision level > 0!");
		
		do {
			if (reason==null) {/* decision or unit clause */
				long id=getClauseId(lit);
				exceptionalCondition(id==0L, "No decisions allowed at level <= 0!");
				
				derivation.addParent(id);
				seen.set(lit2var(lit), true);
			} else if (reason instanceof Integer) { /* binary clause */
				long id=getClauseId(lit, oppositeLit((Integer)reason));
				exceptionalCondition(id==0L, 
						"Binary clause ["+(sign(lit) ? "" : "-")+lit2variable(lit)+", "+
						(sign((Integer)reason) ? "-" : "")+lit2variable((Integer)reason)+"] unknown!");
				
				derivation.addParent(id);
				seen.set(lit2var(lit), true);
				seen.set(lit2var((Integer)reason), true);
			} else { /* reason is clause with |clause|>2 */
				Clause clause=(Clause)reason;
				
				derivation.addParent(clause.getId());
				for (int i=0; i<clause.size(); i++)
					seen.set(lit2var(clause.get(i)), true);
			}
			
			while (trailPointer>=0 && !seen.get(lit2var(trail.get(trailPointer))))
				trailPointer--;
			
			if (trailPointer>=0) {
				lit=trail.get(trailPointer);
				reason=lit2variable(lit).reason();
			} else
				break;
		} while (trailPointer-->=0);
		
		/* clear seen */
		for (trailPointer=0; trailPointer<trail.size(); trailPointer++)
			seen.set(lit2var(trail.get(trailPointer)), false);
		
		emptyClause=derivation;
	}
	
	private void exceptionalCondition(boolean condition, String message) throws Exception {
		if (condition)
			throw new Exception(message);
	}
	
	/*
	 * output derivation: Three parts:
	 * 
	 *   1. Original clauses, which take part in the derivation of the empty clause (i.e., a unsatisfiable core)
	 *   2. Learnt clauses derived from them, starting with the empty clause
	 *   
	 *   e.g.: a+-a:
	 *   
	 *     1: input0: a
	 *     2: input1: -a
	 *     0: 1 2
	 *     
	 *   e.g.: a+(-a/b)+-b
	 *   
	 *     1: input0: a
	 *     2: input1: -a, b
	 *     3: input2: -b
	 *     0: 3 2 1
	 */
	
	public void printDerivation(PrintStream out) {
		if (emptyClause!=null) {
			Set<Long> originals=emptyClause.getOriginalClauses();
			Set<Long> learnts=emptyClause.getDerivationalClauses();
			
			/* output original clauses that participate in the derivation*/
			for (long clause : originals) {
				out.println(id2original.get(clause));
			}
			
			/* output empty clause derivation */
			out.println(emptyClause);
			
			/* output derivations of learnt clauses which took part in the refutation */
			for (long clause : learnts) {
				out.println(getDeductionInformation(clause));
			}
		}
	}
	
	/*
	 * Output the names of the clauses/clause groups that took part in the 
	 * derivation
	 */
	public Set<String> getCoreTags() throws Exception {
		if (emptyClause!=null) {
			Set<String> tags=new HashSet<String>();
			
			for (long clause : emptyClause.getOriginalClauses())
				tags.add(id2original.get(clause).name);
			
			return tags;
		} else
			throw new Exception("No empty clause found, didn't call sat() or input UNSAT?");
	}
	
	/*
	 * print a trace that is suitable formatted to be fed to the proof check 
	 * tracecheck (included in Booleforce-1.2, http://fmv.jku.at/booleforce/)
	 */
	public void printTraceCheckDerivation(PrintStream out) {
		if (emptyClause!=null) {
			Set<Long> originals = emptyClause.getOriginalClauses();
			Set<Long> learnts = emptyClause.getDerivationalClauses();
			
			for (long clause : originals)
				out.println(id2original.get(clause).toTraceCheckEntry(this));
			
			out.println(emptyClause.toTraceCheckEntry());
			
			for (long clause : learnts)
				out.println(getDeductionInformation(clause).toTraceCheckEntry());
		}
	}
}
