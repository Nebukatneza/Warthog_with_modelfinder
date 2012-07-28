package de.stzoit.prover.cnf;

import de.stzoit.prover.collections.ComparableWithIndex;

public class Variable implements ComparableWithIndex<Variable> {
	private CNFSolver.Val value=CNFSolver.Val.UNKNOWN;
	private String name=null;
	private Object reason=null;
	private int score=0;
	private boolean phase=false;
	private long jwh=0;
	private int hind=-1;
	
	public Variable(String vn) {
		name=vn;
	}
	
	public CNFSolver.Val get_value() {
		return value;
	}
	
	public void setValue(CNFSolver.Val val) {
		value=val;
	}
	
	public String getName() {
		return name;
	}
	
	public Object reason() {
		return reason;
	}
	
	public void setReason(Object r) {
		reason=r;
	}
	
	public int getScore() {
		return score;
	}
	
	public void setScore(int s) {
		score=s;
	}
	
	public boolean getPhase() {
		return phase;
	}
	
	public void setPhase(boolean p) {
		phase=p;
	}
	
	public long getJwh() {
		return jwh;
	}
	
	public void setJwh(long j) {
		jwh=j;
	}

	public int compareTo(Variable o) {
		return score-o.getScore();
	}
	
	public String toString() {
		return name;
	}
	
	public void incScore() {
		score++;
	}

	public int index() {
		return hind;
	}
	
	public void setIndex(int i) {
		hind=i;
	}
}
