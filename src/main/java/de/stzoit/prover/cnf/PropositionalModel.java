package de.stzoit.prover.cnf;

import java.util.LinkedList;
import java.util.List;

import de.stzoit.prover.Model;

public class PropositionalModel implements Model {
	private List<Variable> positives;
	private List<Variable> negatives;
	
	public PropositionalModel() {
		positives=new LinkedList<Variable>();
		negatives=new LinkedList<Variable>();
	}
	
	public void pushPositive(Variable variable) {
		positives.add(variable);
	}

	public void pushNegative(Variable variable) {
		negatives.add(variable);
	}

	public String getConjunction(String and, String not) {
		StringBuilder sb=new StringBuilder();
		boolean first=true;
		
		for (Variable v : positives)
			if (first) {
				sb.append(v.getName());
				first=false;
			}
			else
				sb.append(and+v.getName());
		
		for (Variable v : negatives)
			if (first) {
				sb.append(not+v.getName());
				first=false;
			}
			else
				sb.append(and+not+v.getName());
			
		return sb.toString();
	}
	
	private List<String> getNameList(List<Variable> in) {
		List<String> rv=new LinkedList<String>();
		
		for (Variable v : in)
			rv.add(v.getName());
		
		return rv;
	}

	public List<String> getPositiveNames() {
		return getNameList(positives);
	}

	public List<String> getNegativeNames() {
		return getNameList(negatives);
	}

}
