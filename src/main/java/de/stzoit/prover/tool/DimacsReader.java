package de.stzoit.prover.tool;

import java.io.BufferedReader;
import java.io.FileReader;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.TreeSet;

import de.stzoit.prover.cnf.CNFSolver;
import de.stzoit.prover.cnf.Clause;
import de.stzoit.prover.cnf.tracing.ProofTracing;

/**
 * Reads boolean formula given in DIMACS file
 * @author MS
 * @author AK (modified reader to add clauses directly to solver)
 */
public class DimacsReader {
	
	public void readTrace(String filename, ProofTracing solver) throws Exception {
		FileReader fr = new FileReader(filename);
		BufferedReader br = new BufferedReader(fr);
	
		int numberOfVarsInPreamble = 0;
		int numberOfClausesInPreamble = 0;
		boolean preambleRead = false;
		
		Clause clause = new Clause(solver, solver.getNewOriginalId());
		
		int clauseCounter = 0;
		// set with elements of Type Integer (positive), representing variables
		Set<Integer> varCounter = new TreeSet<Integer>();
		
		int lineNumber = 0;
		String line = null;
		while((line = br.readLine()) != null) {
			lineNumber++;
			
			// ignore empty lines
			if(line.length() == 0)
				continue;
			
			// ignore comments (line starts with c)
			if(line.startsWith("c"))
				continue;
			
			// read preamble (line starts with p)
			if(line.startsWith("p")) {
				if(preambleRead) {
					System.err.println("Line " + lineNumber + ": More than one preamble --> Use the first");
					continue;
				}
				StringTokenizer st = new StringTokenizer(line);
				int tokens = st.countTokens();
				if(tokens == 4) {
					try {
						int count = 0;
						while(st.hasMoreTokens()) {
							count++;
							String t = st.nextToken();
							if(count == 3) {
								numberOfVarsInPreamble = Integer.parseInt(t);
							}
							else if(count == 4) {
								numberOfClausesInPreamble = Integer.parseInt(t);
							}
						}
						preambleRead = true;
					} catch(NumberFormatException e) {
						System.err.println("Line " + lineNumber + ": Number format exception in preamble --> Skip line");
					}
				} else {
					System.err.println("Line " + lineNumber + ": Not 4 tokens in preamble --> Skip line");
				}
			} 
			else {
			
				// read clause, read to '0' (must not be in one line)
				try {
					StringTokenizer st = new StringTokenizer(line);
					while(st.hasMoreElements()) {
						String t = st.nextToken();
						int var = Integer.parseInt(t);
						if(var == 0) {
							// end of clause reached
							solver.pushClause(clause);
							clauseCounter++;
							clause = new Clause(solver, solver.getNewOriginalId());
						} else if(var < 0) {
							clause.push(Integer.toString(var));
							
							// add positive var to varCounter
							int posVar = var * -1;
							Integer posVarInteger = new Integer(posVar);
							varCounter.add(posVarInteger);
						} else { // var > 0
							Integer varInteger = new Integer(var);
							varCounter.add(varInteger);
							clause.push(Integer.toString(var));
						}
					}
				} catch(NumberFormatException e) {
					System.err.println("Line " + lineNumber + ": Number format exception --> Skip literal and rest of line");
				}
			}
		
		}
		
		br.close();
		
		// check preamble with computed values
		if(preambleRead) {
			if(varCounter.size() != numberOfVarsInPreamble) {
				System.err.println("Number of Vars in Preamble: " + numberOfVarsInPreamble + 
						", " + 
						"Number of computed Vars: " + varCounter.size());
			}
			
			if(clauseCounter != numberOfClausesInPreamble) {
				System.err.println("Number of Clauses in Preamble: " + numberOfClausesInPreamble + 
						", " + 
						"Number of computed Clauses: " + clauseCounter);
			}
		}
	}
	
	public void readSolve(String filename, CNFSolver solver) 
		throws Exception 
	{
		FileReader fr = new FileReader(filename);
		BufferedReader br = new BufferedReader(fr);
	
		int numberOfVarsInPreamble = 0;
		int numberOfClausesInPreamble = 0;
		boolean preambleRead = false;
		
		Clause clause = new Clause(solver);
		
		int clauseCounter = 0;
		// set with elements of Type Integer (positive), representing variables
		Set<Integer> varCounter = new TreeSet<Integer>();
		
		int lineNumber = 0;
		String line = null;
		while((line = br.readLine()) != null) {
			lineNumber++;
			
			// ignore empty lines
			if(line.length() == 0)
				continue;
			
			// ignore comments (line starts with c)
			if(line.startsWith("c"))
				continue;
			
			// read preamble (line starts with p)
			if(line.startsWith("p")) {
				if(preambleRead) {
					System.err.println("Line " + lineNumber + ": More than one preamble --> Use the first");
					continue;
				}
				StringTokenizer st = new StringTokenizer(line);
				int tokens = st.countTokens();
				if(tokens == 4) {
					try {
						int count = 0;
						while(st.hasMoreTokens()) {
							count++;
							String t = st.nextToken();
							if(count == 3) {
								numberOfVarsInPreamble = Integer.parseInt(t);
							}
							else if(count == 4) {
								numberOfClausesInPreamble = Integer.parseInt(t);
							}
						}
						preambleRead = true;
					} catch(NumberFormatException e) {
						System.err.println("Line " + lineNumber + ": Number format exception in preamble --> Skip line");
					}
				} else {
					System.err.println("Line " + lineNumber + ": Not 4 tokens in preamble --> Skip line");
				}
			} 
			else {
			
				// read clause, read to '0' (must not be in one line)
				try {
					StringTokenizer st = new StringTokenizer(line);
					while(st.hasMoreElements()) {
						String t = st.nextToken();
						int var = Integer.parseInt(t);
						if(var == 0) {
							// end of clause reached
							solver.pushClause(clause);
							clauseCounter++;
							clause = new Clause(solver);
						} else if(var < 0) {
							clause.push(Integer.toString(var));
							
							// add positive var to varCounter
							int posVar = var * -1;
							Integer posVarInteger = new Integer(posVar);
							varCounter.add(posVarInteger);
						} else { // var > 0
							Integer varInteger = new Integer(var);
							varCounter.add(varInteger);
							clause.push(Integer.toString(var));
						}
					}
				} catch(NumberFormatException e) {
					System.err.println("Line " + lineNumber + ": Number format exception --> Skip literal and rest of line");
				}
			}
		
		}
		
		br.close();
		
		// check preamble with computed values
		if(preambleRead) {
			if(varCounter.size() != numberOfVarsInPreamble) {
				System.err.println("Number of Vars in Preamble: " + numberOfVarsInPreamble + 
						", " + 
						"Number of computed Vars: " + varCounter.size());
			}
			
			if(clauseCounter != numberOfClausesInPreamble) {
				System.err.println("Number of Clauses in Preamble: " + numberOfClausesInPreamble + 
						", " + 
						"Number of computed Clauses: " + clauseCounter);
			}
		}
	}
}
