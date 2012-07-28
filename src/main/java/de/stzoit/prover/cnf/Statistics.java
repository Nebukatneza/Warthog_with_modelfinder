package de.stzoit.prover.cnf;

import java.io.PrintStream;

import de.stzoit.prover.TimeOutException;

public class Statistics {
	private int num_restarts               =0;       /* relevant to luby-sequence generation */
	private int num_conflicts              =0;       /* number of conflicts */
	private int conflicts_till_restart_mul =100;     /* some usefull value */
	private int conflicts_left_till_restart=0;       /* initially equal to multiplyer*/
	private int num_decisions              =0;       /* number of decisions */
	private int max_decisions              =1000000; /* deliberately set to 10^6 */
	private int var_decay_factor           =2;       /* decay factor for VSIDS */
	private int var_decay_rate             =256;     /* decay rate for VSIDS */
	private int max_level                  =0;       /* maximum decision level which occured during search */
	private int num_learnt                 =0;       /* holds number of learnt clauses >2 */
	private int num_learnt_bin             =0;       /* holds number of learnt binary clauses */
	private int num_learnt_unit            =0;       /* holds number of learnt unit clauses*/
	private int learntsize_mul             =11;      /* multiply max_learnt by this value for increasing dbsize */
	private int learntsize_div             =10;      /* divide max_learnt ----------------- " ----------------- */
	private int learntsize_init_div        =3;       /* initial fraction for max_learnt */
	private int max_learnt                 =0;       /* set this one before solving via setter method */
	private int enlargement_numerator      =3;       /* */
	private int enlargement_denominator    =2;       /* */
	private int init_confl_till_enlarge    =100;     /* */
	private int confl_till_enlarge_cnt     =0;       /* */
	private int confl_till_enlarge         =0;
	
	public Statistics() {
		conflicts_left_till_restart=luby(1)*conflicts_till_restart_mul;
		confl_till_enlarge=init_confl_till_enlarge;
		confl_till_enlarge_cnt=confl_till_enlarge;
	}
	
	public Statistics(int max_dec) {
		this();
		max_decisions=max_dec;
	}
	
	public void statReset() {
		num_restarts=0;
		num_conflicts=0;
		conflicts_left_till_restart=luby(1)*conflicts_till_restart_mul;
		confl_till_enlarge=init_confl_till_enlarge;
		confl_till_enlarge_cnt=confl_till_enlarge;
		num_decisions=0;
		max_level=0;
		num_learnt=0;
		num_learnt_bin=0;
		num_learnt_unit=0;
		max_learnt=0;
	}
	
	/* return luby sequent at pos i (serves as multiplier for restart intervall) */
	public int luby(int i) {
		int fst=~(((int)~0)>>>1); /* 10...0 */
		
		while ((i&fst)==0 && fst!=0) /* 2^k >= i >= 2^{k-1}=fst */
			fst>>>=1;
			
		if (i==(fst<<1)-1) /* i==2^k-1 */
			return fst;    /* 2^{k-1} */
		else
			return luby(i-(fst-1)); /* luby(i-(2^{k-1}-1)) */
	}
	
	public void statRestart() {
		num_restarts++;
		conflicts_left_till_restart=luby(num_restarts)*conflicts_till_restart_mul;
	}
	
	public void statDecide() throws TimeOutException {
		if (max_decisions<=num_decisions) {
			//System.out.println("Max. decisions reached, timeout");
			throw new TimeOutException("Max. decisions ("+max_decisions+") reached, timeout");
		}
		num_decisions++;
	}
	
	public void stat_reset_decisions() {
		num_decisions=0;
	}
	
	public void statConflict() {
		num_conflicts++;
		conflicts_left_till_restart--;
		confl_till_enlarge_cnt--;
		
		if (statDoEnlarge())
			statEnlarge();
	}
	
	public int getConflictsTillRestartMul() {
		return conflicts_till_restart_mul;
	}
	
	public int statGetDecayFactor() {
		return var_decay_factor;
	}
	
	public int statGetDecayRate() {
		return var_decay_rate;
	}
	
	public int statGetMaxDecisions() {
		return max_decisions;
	}
	
	public int statGetConflictsLeftTillRestart() {
		return conflicts_left_till_restart;
	}
	
	public boolean statPerformRestart() {
		return conflicts_left_till_restart==0;
	}
	
	public int statGetNumDecisions() {
		return num_decisions;
	}
	
	public boolean statPerformDecaying() {
		return (num_decisions%var_decay_rate)==0;
	}
	
	public void statLearnUnit() {
		num_learnt_unit++;
	}
	
	public void statLearnBin() {
		num_learnt_bin++;
	}
	
	public void statLearn() {
		num_learnt++;
	}
	
	public int statGetMaxLearnt() {
		return max_learnt;
	}
	
	public void statSetMaxLearnt(int m) {
		/* one might always learnt >= 2000 clauses */
		max_learnt=Math.max(2000, (m/learntsize_init_div));
		confl_till_enlarge=init_confl_till_enlarge;
		confl_till_enlarge_cnt=confl_till_enlarge;
	}
	
	public void statIncMaxLearnt() {
		max_learnt=(max_learnt*learntsize_mul)/learntsize_div;
	}
	
	public void statEnlarge() {
		statIncMaxLearnt();
		confl_till_enlarge=(confl_till_enlarge*enlargement_numerator)/enlargement_denominator;
		confl_till_enlarge_cnt=Math.max(init_confl_till_enlarge, Math.abs(confl_till_enlarge));
	}
	
	public boolean statDoEnlarge() {
		return confl_till_enlarge_cnt<=0;
	}
	
	public void maxLevel(int level) {
		max_level=(max_level<level ? level : max_level);
	}
	
	public void statPrint(PrintStream out) {
		if (out==null)
			return;
		
		out.println("c ----------------------------------------------------------------------");
		out.println("c Statistics: ");
		out.println("c ----------------------------------------------------------------------");
		out.println("c #Decisions:           "+num_decisions);
		out.println("c #Conflicts:           "+num_conflicts);
		out.println("c #Restarts:            "+num_restarts);
		out.println("c #Learnt Clauses:      "+num_learnt);
		out.println("c #Learnt bin. Clauses: "+num_learnt_bin);
		out.println("c #Learnt unit Clauses: "+num_learnt_unit);
		out.println("c Max. Level: "+max_level);
	}
}
