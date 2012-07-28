package de.stzoit.prover.cnf;

import java.io.PrintStream;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;

import de.stzoit.prover.Model;
import de.stzoit.prover.NotSATException;
import de.stzoit.prover.Solver;
import de.stzoit.prover.TimeOutException;
import de.stzoit.prover.collections.HeapWithIndex;
import de.stzoit.prover.collections.IVec;
import de.stzoit.prover.collections.Vec;
import de.stzoit.prover.collections.nativeType.BooleanVec;
import de.stzoit.prover.collections.nativeType.IntVec;


/**
 * Optimized CNF solver
 * 
 *     - deals with binary and unit clauses separately
 *         * learnt binary & unit clauses are never removed by clause garbage collection
 *         * binary clauses are represented in terms of adjacency lists of literals for fast propagation
 *         * binary clauses are propagated before longer clauses are propagated
 *       drawback:
 *         * due to the special representation of binary clauses, we need to copy stack bounds for every binary 
 *           watchlist entry
 *     - for context saving, there are two options:
 *         1. completely restart (i.e. start over from level 0), when backtracking to a mark known to be 
 *            satisfiable
 *         2. save all the decisions involved in the satisfiable solution previously found for the mark, thus 
 *            being able to restore the solution context when calling undo()
 *       whether option 1 or 2 pays off has to be evaluated experimentally
 *     - heuristics
 *         * variable phases:
 *             1. Jeroslow-Wang for initial phases
 *             2. always positive
 *             3. always negative
 *             4. phase saving (remember variable phase while backtracking)
 *         * branching:
 *             1. VSIDS (variable state independent decaying sum), MiniSAT-like style (start off from 0, increase 
 *                variable instead of literal scores)
 *         * clause elimination:
 *             1. MiniSAT style heuristic: increase scores for learnt clauses involved in conflicts, decrease 
 *                scores after deletion
 *             2. Glucose style heuristics: calculate LBD (level block distance, i.e. distinct levels in conflict 
 *                clause) and use it as a measure of clause usefulness
 *     - Default settings:
 *         * Jeroslow-Wang-like scoring for initial phases
 *         * Phase saving activated
 *         * VSIDS with decaying every 256 decisions by 4
 *         * Glucose style clause activity, allow at least 2000 conflict clauses to be saved
 *         * faster backtracking (instead of faster assignment)
 *         * Luby restarts (multiplier: 100 conflicts) 
 * 
 * @author AK
 *
 */
public class CNFSolver implements Solver {
	@SuppressWarnings("unused")
	private static final long serialVersionUID = 1L;
	
	public enum Val { 
		FALSE, UNKNOWN, TRUE;
		public static synchronized Val neg(Val v) {
			return ((v==FALSE) ? TRUE : ((v==TRUE) ? FALSE : UNKNOWN));
		}
		
		public static synchronized Val valueOf(boolean b) {
			return b ? TRUE : FALSE;
		}
	};
	protected enum State { SAT, UNSAT, UNKNOWN };
	
	protected static final String version="0.0.1";             /* version number                                */
	protected Statistics stats;                                /* statistics                                    */
	protected IVec<IVec<Clause>> watchlists;        /* watches (positive and negative) for variables */
	protected IVec<IntVec> binwatchlists;                      /* watches for binary clauses                    */
	protected IVec<Clause> origclauses;             /* holds original clauses                        */
	protected IVec<LearntClause> learntclauses;     /* holds learnt clauses                          */
	protected IVec<Variable> variables;             /* holds variables, implicitly provides Int->Var */
	protected IntVec trail;                                    /* trail/assignment stack/propagation queue      */
	protected IntVec unitfacts;                                /* unit clauses                                  */
	protected IntVec levels;                                   /* Lit->Integer level at which lit was assigned  */
	protected BooleanVec seen;                                 /* marks used during conflict resolution         */
	protected IntVec perm_diff;                                /* helper structure for calculation LBD          */
	protected IVec<Integer[]> marks;                           /* marks for {in,de}cremental SAT solving        */
	protected int level=0;                                     /* current decision level                        */
	protected int trail_lim=0;                                 /* trail index from which to start propagation   */
	protected Object conflict_reason=null;                     /* contains a reason in case of conflict         */
	protected boolean bt2zero_after_unit_addition=true;        /* if true always backtrack to 0 uppon addition  
	                                                            of unit clauses                               */
	protected boolean phase_saving=true;                       /* perform phase saving uppon backtracking       */
	protected HashMap<String,Integer> name2var=null;           /* mapping of variables names to numbers         */
	protected HeapWithIndex<Variable> varq=null;    /* holds */
	protected State state=State.UNKNOWN;
	protected char initial_phase=2;                            /* 0 false, 1 true, 2 ~JWH                       */
	protected int conflict_lit=0;                              /* conflicting literal implied by binary clause  */
	protected int permdiff_curr=0;                             /* flag for measuring learnt clause LBD          */
	protected boolean glucose_clause_scores=false;              /* glucose-style static clause activity measure  */
	protected boolean perform_clause_deletion=false;            /* weed out learnt clauses from time to time     */
	protected int tseitin_bound=50;                            /* bound on formula length for Tseitin transf.   */

	protected String name=null;                                /* solver name */
	protected Val value_enum=null;
	protected boolean score_saving=false;                      /* save scores/phases on mark(), reset on undo() */
	
	public CNFSolver() {
		stats        =new Statistics(25000000); /* max. decisions deliberately set to 25*10^6 */
		watchlists   =new Vec<IVec<Clause>>();
		binwatchlists=new Vec<IntVec>();
		origclauses  =new Vec<Clause>();
		learntclauses=new Vec<LearntClause>();
		variables    =new Vec<Variable>();
		trail        =new IntVec();
		unitfacts    =new IntVec();
		levels       =new IntVec();
		perm_diff    =new IntVec();
		seen         =new BooleanVec();
		name2var     =new HashMap<String,Integer>();
		varq         =new HeapWithIndex<Variable>();
		marks        =new Vec<Integer[]>();
		
		/* variables 0 and 1 are reserved */
		watchlists.push(null); watchlists.push(null);
		binwatchlists.push(null); binwatchlists.push(null);
		variables.push(null);
		levels.push(-1);
		seen.push(false);
		perm_diff.push(-1);
	}
	
	public CNFSolver(String n) {
		this();
		name=n;
	}
	
	public int newVariable(String name) {
		int vnum=variables.size();
		Variable var=new Variable(name==null ? "__V"+vnum : name);
		
		watchlists.push(new Vec<Clause>());
		watchlists.push(new Vec<Clause>());
		binwatchlists.push(new IntVec());
		binwatchlists.push(new IntVec());
		variables.push(var);
		levels.push(-1);
		perm_diff.push(-1);
		seen.push(false);
		name2var.put(var.getName(), vnum);
		varq.insert(var);
		
		return vnum;
	}
	
	public boolean varExists(String name) {
		return name2var.get(name)!=null;
	}
	
	public int getVariable(String name) {
		return name2var.get(name);
	}
	
	public static int lit2var(int lit) {
		return lit/2;
	}
	
	public Variable lit2variable(int lit) {
		int var=lit2var(lit);
		if (var<variables.size())
			return variables.get(var);
		return null;
	}
	
	public Val lit2val(int lit) {
		return lit2variable(lit)!=null 
		         ? (sign(lit) ? lit2variable(lit).get_value() : Val.neg(lit2variable(lit).get_value())) 
		         : Val.UNKNOWN;
	}
    
    public static Val litValue(int lit) {
        return sign(lit) ? Val.TRUE : Val.FALSE;
    }
	
	/* true: positive literal, false: negative literal */
	public static boolean sign(int lit) {
		return lit%2==1;
	}
	
	public static String toDimacsLit(int lit) {
		return (sign(lit) ? "" : "-")+lit2var(lit);
	}
	
	public String lit2String(int lit) {
		return (sign(lit) ? "" : "-")+lit2var(lit);
	}
	
	public static int var2lit(int var, boolean sign) {
		return 2*var+(sign ? 1 : 0);
	}
	
	public int oppositeLit(int lit) {
		return lit+(sign(lit) ? -1 : 1);
	}
	
	/* 
	 * guarded assign: returns false if a conflict has been detected 
	 * (i.e. when trying to assign values opposite to the current value); true else. If lit is UNKNOWN before 
	 * assignment, lit is added to the trail 
	 * 
	 * possible reasons:
	 *     i)   null: Decision
	 *     ii)  Integer i, i=lit: Unit
	 *     iii) Integer i, i!=lit: Binary clause (i \/ lit)
	 *     iv)  RefurbishedClause: standard BCP due to clause (l_0 \/ ... \/ l_n \/ lit), l_0 -> 0, ..., l_n -> 0
	 */
	public boolean assign(int lit, Object reason) {
		/* assign value induced by lit i.e. lit=-i -> i=FALSE, lit=i -> i=TRUE */
		Val newval=Val.valueOf(sign(lit));
		Variable var=lit2variable(lit);
		
		if (var!=null && (var.get_value()==newval || var.get_value()==Val.UNKNOWN)) {
			if (var.get_value()==Val.UNKNOWN) {
				var.setValue(newval);
				var.setReason(reason);
				
				trail.push(lit);
				levels.set(lit2var(lit), level);
				varq.delete(var);
				
				if (reason!=null && reason instanceof LearntClause)
					((LearntClause)reason).ref(); /* increment reference counter */
			}
			return true;
		}
		else { /* CONFLICT! */
			conflict_lit=lit;
			conflict_reason=reason;
			return false;
		}
	}
	
	protected void unassign(int lit) {
		Variable v=lit2variable(lit);
		
		if (v!=null) {
			if (v.reason() instanceof LearntClause)
				((LearntClause)v.reason()).deref();
			
			v.setReason(null);
			v.setValue(Val.UNKNOWN);
			if (phase_saving)
				v.setPhase(sign(lit));
			varq.quickInsert(v);
			
			levels.set(lit2var(lit), -1);
		}
	}
	
	/* returns false if a conflict has been detected */
	protected boolean bcp() {
		while (trail_lim<trail.size()) {
			int lit                   =trail.get(trail_lim++);
			IntVec bwl         =binwatchlists.get(lit);
			IVec<Clause> wl=watchlists.get(lit);

			/* propagate binary clauses first */
			for (int i=0; i<bwl.size(); i++)
				if (!assign(bwl.get(i), lit)) {		
					return false;
				}
			
			/* try to move watches for every clause in the watchlist of lit */
			int i=0;
			while (i<wl.size()) {
				switch (wl.get(i).moveWatch(oppositeLit(lit), i)) {
					case -1: /* assignment failed */		
						return false;
					case  0: /* watch not moved */
						i++;
						break;
					case  1: /* watch moved */
						break;
				}
			}
		}		
		return true;
	}
	
	/* 
	 * add original clause: true if successful, false if conflicting
	 */
	public boolean pushClause(Clause cls) throws Exception {
		/* check clause */
		if (cls.isTautology()) {
			return true;
		}
		
		if (!cls.isLearnt())
			backtrack(0, true);
		
		if (cls.size()==0) {
			state=State.UNSAT;
		}
		else if (cls.size()==1) {
			if (state!=State.UNSAT && level>0) { /* backtrack to a) Level 0, b) Level beneath get_level(cls[0]) */
				backtrack(0, true);
			}
			
			unitfacts.push(cls.get(0));
			if (cls.isLearnt())
				stats.statLearnUnit();
			
			if (state!=State.UNSAT && !assign(cls.get(0), null)) /* do not perform assign if state==UNSAT */ {
				state=State.UNSAT;
			}
		}
		else {
			if (state!=State.UNSAT && !cls.sat() && !cls.isLearnt()) {
				backtrack(0, true);
				long packed=cls.bothLargestDecisionLevels();
				
				if (packed==0L) { /* all literals failed and assigned at level 0 */
					state=State.UNSAT;
					return false;
				}
				else if (cls.unpackHigher(packed)==-1 && cls.unpackLower(packed)==-1) /* >= 2 literals unassigned */
					;
				else if (cls.unpackLower(packed)==-1) {
					if (cls.unpackHigher(packed)==0) { /* propagate */
						if (!assign(cls.get(1), (cls.size()>2 ? cls : oppositeLit(cls.get(0))))) {
							state=State.UNSAT;
							return false;
						}							
					} 
					else {
						backtrack(Math.max(0, cls.unpackHigher(packed)-1), true);
					}
				}
				else {
					backtrack(Math.max(0, cls.unpackLower(packed)-1), true);
				}
			} else if (state!=State.UNSAT && !cls.sat() /* && level>0 */ && cls.isLearnt()) {
				/* 
				 *      by convention, learnt clauses of length >= 2 include the asserted literal at position 0
				 *      and a literal assigned at the highest decision level beneath the assertion level at 
				 *      position 1.
				 */
				backtrack(Math.max(0, getLevel(cls.get(1))));
			}
			
			if (cls.size()==2) {

				IntVec bwl0=binwatchlists.get(oppositeLit(cls.get(0)));
				IntVec bwl1=binwatchlists.get(oppositeLit(cls.get(1)));
				
				bwl0.push(cls.get(1));
				bwl1.push(cls.get(0));
				
				if (cls.isLearnt())
					stats.statLearnBin();
			} else { /* >2 */
				IVec<Clause> wl0=watchlists.get(oppositeLit(cls.get(0)));
				IVec<Clause> wl1=watchlists.get(oppositeLit(cls.get(1)));
				
				wl0.push(cls);
				wl1.push(cls);
				
				if (cls.isLearnt()) {
					stats.statLearn();
					learntclauses.push((LearntClause) cls);
				}
				else
					origclauses.push(cls);
			}
		}
		if (initial_phase==2 && level==0 && state!=State.UNSAT)
			cls.incJwh();
		
		/* after adding a clause, the solver state is at least UNKNOWN if not UNSAT */
		if (state!=State.UNSAT)
			state=State.UNKNOWN;
		
		return state!=State.UNSAT;
	}
	
	/* true if clause has been detached, false otherwise */
	protected boolean detachClause(Clause cls) {
		if (cls!=null && cls.size()>2) {
			/* delete clause from watchlists */
			IVec<Clause> wl0=watchlists.get(oppositeLit(cls.get(0))),
			                        wl1=watchlists.get(oppositeLit(cls.get(1)));
			
			wl0.remove(cls);
			wl1.remove(cls);
			
			return true;
		}
		return false;
	}
	
	/* backtrack to decision level l, if l<0 everything is erased */
	protected void backtrack(int l) {
		boolean did_unassign=(level>l && trail.size()>0);
		while ((l>=0 && level>l && trail.size()>0) || (l<0 && trail.size()>0)) {
			Variable v=lit2variable(trail.last());
			
			if (v!=null) {
				if (v.reason()==null) { /* i.e. decision */
					level--;
				}
				unassign(trail.last());
			}
			
			trail.pop();
		}
		if (l<0)
			level=0;

		trail_lim=trail.size();
		if (did_unassign)
			varq.restoreHeapProperty();
	}
	
	protected void backtrack(int l, boolean prop_preserve) {
		boolean did_unassign=(level>l && trail.size()>0);
		while ((l>=0 && level>l && trail.size()>0) || (l<0 && trail.size()>0)) {
			Variable v=lit2variable(trail.last());
			
			if (v!=null) {
				if (v.reason()==null) { /* i.e. decision */
					level--;
				}
				unassign(trail.last());
			}
			
			trail.pop();
		}
		if (l<0)
			level=0;
		if (prop_preserve) {
			if (did_unassign)
				trail_lim=trail.size();
		}
		else
			trail_lim=trail.size();
			
		if (did_unassign) {
			varq.restoreHeapProperty();
		}
	}
	
	private void decay() {
		/* start from 1 as 0 is reserved as DIMACS clause terminator */
		for (int i=1; i<variables.size(); i++) {
			Variable var=variables.get(i);
			var.setScore(var.getScore()>>>stats.statGetDecayFactor());
		}
		varq.restoreHeapProperty();
	}
	
	protected boolean decide() throws TimeOutException {
		if (varq.isEmpty()) /* SAT! */
			return false;
		else {
			level++;
			stats.maxLevel(level);
			stats.statDecide();
			if (stats.statPerformDecaying())
				decay();
			
			Variable var=varq.heapExtractMax();
			
			assign(var2lit(getVariable(var.getName()), var.getPhase()), null);
			
			return true;
		}
	}
	
	/* conflict handling */	
	protected void handleConflict() throws Exception {
		LearntClause learnt=new LearntClause(this);
		int i=trail.size()-1,
		    n=0,
		    lit=0;
		Object reason=conflict_reason;
		
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
						learnt.push((Integer)reason);
					}
				}
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
		
		/* ATTENTION HERE: might return false (e.g. unit deduced but unit already set => UNSAT) */
		pushClause(learnt);
		/* don't assign uip if restart was performed and the asserting level of the learnt clause is >0 */
		if (learnt.size()>1 && (!do_restart||bt_level==0)) {
			assign(learnt.get(0), (learnt.size()==2 ? oppositeLit(learnt.get(1)) : learnt));
		}
	}
	
	/* clause management */
	
	public void removeFromWatchlist(int lit, int ind) {
		if (lit<watchlists.size() && ind<watchlists.get(lit).size())
			watchlists.get(lit).delete(ind);
	}
	
	public void addToWatchlist(int lit, Clause clause) {
		if (lit<watchlists.size())
			watchlists.get(lit).push(clause);
	}
	
	public int getLevel(int lit) {
		if (lit<watchlists.size())
			return levels.get(lit2var(lit));
		return -1;
	}

	public Model getModel() throws Exception {
		if (state==State.UNKNOWN)
			sat();
		if (state!=State.SAT || trail.size()<=0)
			throw new NotSATException("Solver state is not SAT or trail size is less than or equal 0");
		
		Model rv=new PropositionalModel();
		for (int i=0; i<trail.size(); i++) {
			Variable v=lit2variable(trail.get(i));

			if (sign(trail.get(i)))
				rv.pushPositive(v);
			else
				rv.pushNegative(v);
		}
		
		return rv;
	}

	/*
	 * Marking information:
	 * 
	 * +--------+------+------+---------+---------+-------+-----------+
	 * | status | orig | vars | w-lists | learnts | units | binary... |
	 * +--------+------+------+---------+---------+-------+-----------+
	 * 
	 * status:  satisfiability status (-1: UNSAT, 0: UNKNOWN, 1: SAT)
	 * orig:    clauses of length >2 at time of marking (stack bound)
	 * vars:    variables at time of marking (stack bound)
	 * w-lists: watchlists (stack bound)
	 * learnts: learnt clauses at time of marking (stack bound)
	 * units:   unit clauses at time of marking (stack bound)
	 * binary:  array of stack bounds for binary clauses (adjacency list lengths)
	 */
	public void save() throws Exception {
		Integer mark[];
		if (!score_saving)
			mark=new Integer[6+binwatchlists.size()];
		else
			mark=new Integer[6+binwatchlists.size()+(variables.size()-1)];
		
		mark[0]=(state==State.UNSAT ? -1 : (state==State.SAT ? 1 : 0)); /* satisfiability status */
		mark[1]=origclauses.size();                                     /* #original clauses */
		mark[2]=variables.size();                                       /* #variables */
		mark[3]=watchlists.size();                                      /* size of n-ary watchlists (n>2) */
		mark[4]=learntclauses.size();                                   /* #learnt clauses */
		mark[5]=unitfacts.size();                                       /* #unit clauses */
		
		/* save sizes of binary watchlists/adjacency lists */
		for (int i=0; i<binwatchlists.size(); i++) {
			if (binwatchlists.get(i)!=null) {
				mark[i+6]=binwatchlists.get(i).size();
			}
			else {
				mark[i+6]=-1;
			}
		}
		if (score_saving)
			saveScoresAndPhases(mark, 6+binwatchlists.size());
		
		/* push marking on marks stack */
		marks.push(mark);
	}
	
	protected void saveScoresAndPhases(Integer mark[], int offset) {
		if (mark.length < (offset+variables.size()-1))
			return;
		for (int i=1; i<variables.size(); i++) {
			Variable var = variables.get(i);
			mark[offset+(i-1)] = ((var.getScore()<<1)|(var.getPhase() ? 0x1 : 0x0));
		}
	}
	
	protected void resetScoresAndPhases(Integer mark[], int offset) {
		for (int i=offset; i<mark.length; i++) {
			int idx=(i-offset)+1;
			
			if (!(idx<variables.size()))
				break;
			
			Variable var = variables.get(idx);
			
			var.setScore((mark[i]>>>1));
			var.setPhase(((mark[i]&0x1) > 0));
		}
		varq.restoreHeapProperty();
	}

	public void release() throws Exception {
		reset();
	}

	public void reset() throws Exception {
		/* discard whole formula, clean up all data structures */
		backtrack(-1);      /* clear trail and reasons */
		stats.statReset();
		state=State.UNKNOWN;
		permdiff_curr=0;
		conflict_reason=null;
		
		/* clear clause structures */
		learntclauses.clear(); /* clear learnt clauses */
		unitfacts.clear();     /* clear unit clauses */
		origclauses.clear();   /* clear original clauses */
		
		/* clear watchlists */
		watchlists.shrinkTo(2);
		binwatchlists.shrinkTo(2);
		
		variables.shrinkTo(1); /* clear variables */
		levels.shrinkTo(1);    /* clear levels */
		varq.clear();          /* clear variable queue */
		seen.shrinkTo(1);      /* clear seen */
		perm_diff.shrinkTo(1); /* clear perm_diff */
		name2var.clear();      /* clear name variable mapping */
		
		/* {in,de}cremental structures */
		marks.clear();         /* clear marks */
		
		/* suggest GC */
		System.gc();
	}
	
	protected void weedOutLearnt() {
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
					detachClause(l[i]);
					learntclauses.set(learntclauses.indexOf(l[i]), null);
					deleted++;
				}
			}
		else
			for (int i=0; i<l.length && deleted<=l.length/2; i++) {
				if (l[i]!=null && !l[i].is_locked()) { /* delete clause */
					detachClause(l[i]);
					learntclauses.set(learntclauses.indexOf(l[i]), null);
					deleted++;
				}
			}
		if (deleted>0) {
			compactify();
			System.gc(); /* perform garbage collection */
		}
	}
	
	/* if we do {in,de}cremental sat-solving, saved stack bounds have to be adjusted */
	protected void compactify() {
		int i, j, k=0;
		Integer mark[]=marks.size()>0 ? marks.get(k) :  null;
		for (i=0, j=0; i<learntclauses.size(); i++) {
			if (mark!=null && i==mark[4]) {
				mark[4]=j; /* learnts of this marking now j */
				mark=(marks.size()>k ? marks.get(k++) : null);
			}
			if (learntclauses.get(i)!=null) {
				/* adjust score... */
				learntclauses.set(j++, learntclauses.get(i));
			}
		}
		/* if last mark's bound equals previous learntclauses' size, adjust it here (as i<learntclauses.size()) */
		if (mark!=null && mark[4]==learntclauses.size())
			mark[4]=j;
		/* from here on, j ... learntclauses.size() may be deleted */
		learntclauses.shrinkTo(j);
	}

	public boolean sat() throws Exception {
		/* initialize max. learnt clause db size */
		stats.statSetMaxLearnt(origclauses.size());
		
		if (state==State.UNSAT) {
			return false;
		}
		else {
			while (true) {
				if (!bcp()) {
					if (level==0) {
						state=State.UNSAT;
						return false;
					}
					handleConflict();
					
					if (state==State.UNSAT) ;
				} else {
					/* reduce db */
					if (perform_clause_deletion && learntclauses.size()-trail.size() > stats.statGetMaxLearnt())
					{
						weedOutLearnt();
					}
					/* perform decision */
					if (!decide()) {
						state=State.SAT;
						return true;
					}
				}
			}
		}
	}
	
	private int numBinClauses() {
		int rv=0;
		for (int i=0; i<binwatchlists.size(); i++) {
			IntVec bwl=binwatchlists.get(i);
			if (bwl!=null)
				for (int j=0; j<bwl.size(); j++)
					if (oppositeLit(i)<bwl.get(j))
						rv++;
		}
		return rv;
	}
	
	public void printDimacs(PrintStream out) {
		int num_vars=variables.size()-1,
		    num_clss=unitfacts.size()+numBinClauses()+origclauses.size();
		
		/* head */
		out.println("p cnf "+num_vars+" "+num_clss);
		
		/* unit clauses */
		for (int i=0; i<unitfacts.size(); i++)
			out.println(lit2String(unitfacts.get(i))+" 0");
		
		/* binary clauses */
		for (int i=0; i<binwatchlists.size(); i++) {
			IntVec bwl=binwatchlists.get(i);
			int lit0=oppositeLit(i);
			
			if (bwl!=null) {
				for (int j=0; j<bwl.size(); j++) {
					int lit1=bwl.get(j);
					if (lit0<lit1)
						out.println(lit2String(lit0)+" "+lit2String(lit1)+" 0");
				}
			}
		}
		
		/* c\in origclauses, |c|>2 */
		for (int i=0; i<origclauses.size(); i++) {
			Clause cls=origclauses.get(i);
			
			if (cls!=null)
				out.println(cls.toString());
		}
	}
	
	/* verify truth assignment: true if every clause contains (at least) one true literal */
	public boolean verify() {
		/* unit clauses */
		for (int i=0; i<unitfacts.size(); i++) {
			/* each unit has to be assigned TRUE */
			if (lit2val(unitfacts.get(i))!=Val.TRUE)
				return false;
		}
		
		/* check binary clauses */
		for (int i=0; i<binwatchlists.size(); i++) {
			IntVec bwl=binwatchlists.get(i);
			int lit0=oppositeLit(i);
			
			if (bwl!=null)
				for (int j=0; j<bwl.size(); j++) {
					if (!(lit2val(lit0)==Val.TRUE || lit2val(bwl.get(j))==Val.TRUE))
						return false;
				}
		}
		
		/* check clauses c with |c|>2 */
		for (int i=0; i<origclauses.size(); i++) {
			Clause cls=origclauses.get(i);
			
			if (cls!=null && !cls.sat())
				return false;
		}
		return true;
	}

	/*
	 * Marking information:
	 * 
	 * +--------+------+------+---------+---------+-------+-----------+
	 * | status | orig | vars | w-lists | learnts | units | binary... |
	 * +--------+------+------+---------+---------+-------+-----------+
	 * 
	 * status:  satisfiability status (-1: UNSAT, 0: UNKNOWN, 1: SAT)
	 * orig:    clauses of length >2 at time of marking (stack bound)
	 * vars:    variables at time of marking (stack bound)
	 * w-lists: watchlists (stack bound)
	 * learnts: learnt clauses at time of marking (stack bound)
	 * units:   unit clauses at time of marking (stack bound)
	 * binary:  array of stack bounds for binary clauses (adjacency list lengths)
	 */
	public void pop() throws Exception {
		stats.statReset(); /* else number of decisions will produce timeout from one point in solving */
		if (marks.size()<=0) {
			return;
		}
		else if (marks.last().length<6) {
			throw new Exception("Mark supposed to contain more than 6 bounds");
		}
		else {
			Integer mark[]=marks.last();
			int binlength=(score_saving ? (mark.length-6-(mark[2]-1)) : mark.length-6);
			int shrinkTo=0;
			
			marks.pop();
			backtrack(-1); /* must be performed here, otherwise GC might have erased clauses before deref'ing */
			
			/* restore solver state */
			state=(mark[0]<0 ? State.UNSAT : State.UNKNOWN);
			
			/* shrink clauses */
			shrinkTo=Math.max(0, Math.min(origclauses.size(), mark[1]));
			for (int i=origclauses.size()-1; i>=shrinkTo; i--)
				detachClause(origclauses.get(i));
			origclauses.shrinkTo(shrinkTo);
			
			/* shrink learnts */
			shrinkTo=Math.max(0, Math.min(learntclauses.size(), mark[4]));
			for (int i=learntclauses.size()-1; i>=shrinkTo; i--)
				detachClause(learntclauses.get(i));
			learntclauses.shrinkTo(shrinkTo);
			
			/* shrink variables */
			shrinkTo=Math.max(0, Math.min(variables.size(), mark[2]));
			
			for (int i=shrinkTo; i<variables.size(); i++) {
				if (variables.get(i).getName()!=null) {
					name2var.remove(variables.get(i).getName());
				}
				if (variables.get(i).index()<0)
					/* System.out.println("*** variable to be removed has index < 0 => no removed from varq!!!") */;
				else
					;
				varq.delete(variables.get(i));
			}
			variables.shrinkTo(shrinkTo);
			
			/* shrink watchlists */
			watchlists.shrinkTo(Math.min(watchlists.size(), mark[3]));
			
			/* shrink units */
			unitfacts.shrinkTo(Math.min(unitfacts.size(), mark[5]));
			
			/* shrink binary watchlists */
			binwatchlists.shrinkTo(Math.min(binwatchlists.size(), binlength));
			
			for (int i=6; i<mark.length; i++) {
				if (i-6 >= binwatchlists.size())
					break;
				
				IntVec bwl=binwatchlists.get(i-6);
				if (bwl!=null && mark[i]>=0)
					bwl.shrinkTo(Math.min(bwl.size(), mark[i]));
			}
			
			if (state!=State.UNSAT) { /* assign unitfacts */
				for (int i=0; i<unitfacts.size(); i++)
					if (!assign(unitfacts.get(i), null)) {
						state=State.UNSAT;
						return;
					}
			}
			if (score_saving)
				resetScoresAndPhases(mark, 6+binlength);
		}
	}
	
	public void stats(PrintStream out) {
		stats.statPrint(out);
	}
	
	protected void banner(PrintStream out) {
		out.println( 
		    "c ----------------------------------------------------------------------\n"
		   +"c ProverNG v"+version+"\n"
		   +"c \n"
		   +"c     (C) 2012 by Andreas J. Kuebler <andreas.kuebler@stw.de>, STZOIT\n"
		   +"c \n"
		   +"c ----------------------------------------------------------------------\n"
		   +"c Options:\n"
		   +"c     initial phase: "+(initial_phase==0 ? "neg." : (initial_phase==1 ? "pos." : "Jeroslow-Wang"))+"\n"
		   +"c     phase saving:  "+(phase_saving ? "enabled" : "disabled")+"\n"
		   +"c     backtrack 0:   "+(bt2zero_after_unit_addition ? "enabled" : "disabled")+"\n"
		   +"c     max.decisions: "+stats.statGetMaxDecisions()+"\n"
		   +"c     restart c.mul: "+stats.statGetConflictsLeftTillRestart()+"\n"
		   +"c     decay rate:    "+stats.statGetDecayRate()+"\n"
		   +"c     decay factor:  "+stats.statGetDecayFactor()+"\n"
		   +"c \n"
		   +"c Num. clauses > 2:  "+origclauses.size()+"\n"
		   +"c Num. variables:    "+variables.size()+"\n"
		   +"c Num. var. in q:    "+varq.size()+"\n"
		   +"c Num. init. unit:   "+unitfacts.size()+"\n"
		   +"c "
		);
	}
	
	protected void printModel() {
		try {
			List<String> model=getModel().getPositiveNames();
			System.out.print("c Solution: ");
			if (model!=null)
				for (String s : model)
					System.out.print(s+" ");
			System.out.print("\n");
			System.out.flush();
		} catch (Exception e) {
			e.printStackTrace();
		}
	}
	
	protected void printTrail() {
		int nass[]=new int[variables.size()];
		System.out.print("c Trail: ");
		for (int i=0; i<trail.size(); i++) {
			System.out.print((sign(trail.get(i)) ? "" : "-")+lit2var(trail.get(i))+" ");
			nass[lit2var(trail.get(i))]++;
		}
		for (int i=0; i<nass.length; i++) {
			if (nass[i]>1)
				System.out.println("c Variable "+i+" assigned "+nass[i]+" times!!!");
		}
		System.out.print("\n");
		System.out.flush();
	}

}
