package de.stzoit.prover.tool;

import de.stzoit.prover.cnf.CNFSolver;
import de.stzoit.prover.cnf.tracing.ProofTracing;

/**
 * 2010/07/19
 * 
 * commandline tool to invoke sat-solver (input format: DIMACS cnf format)
 * 
 * @author AK
 *
 */
public class CmdLineSolver {

	/**
	 * @param args 
	 * @throws Exception 
	 */
	public static void main(String[] args) throws Exception {
		if (args.length!=3)
			usage();
		else {
			
			if (!args[1].equals("-dimacs")) {
				System.err.println("Unknown format: "+args[1]);
				usage();
			}
			
			if (args[0].equals("-solve")) {
				CNFSolver solver=new CNFSolver("cmdlineSolver");

				readAndAddDimacsSolve(args[2], solver);
				
				long start=System.currentTimeMillis();
				boolean rv=solver.sat();
				long end=System.currentTimeMillis();
				
				printTimingAndState(start, end, rv);

			} else if (args[0].equals("-trace")) {
				ProofTracing solver = new ProofTracing("cmdlineTracer");

				readAndAddDimacsTrace(args[2], solver);
				
				long start=System.currentTimeMillis();
				boolean rv=solver.sat();
				long end=System.currentTimeMillis();
				
				if (rv)
					printTimingAndState(start, end, rv);
				else
					solver.printTraceCheckDerivation(System.out);
			} else {
				System.err.println("Unknown solving mode "+args[0]);
				usage();
			}
		}
	}
	
	protected static void printTimingAndState(long start, long end, boolean sat) {
		long s=(end-start)/1000;
		long ms=(end-start)%1000;
		
		System.out.println("c Solving took "+s+"s "+ms+"ms");
		System.out.println("s "+(sat ? "SATISFIABLE" : "UNSATISFIABLE"));
	}
	
	protected static void usage() {
		System.err.println("Usage: CmdLineSolver [-solve|-trace] -dimacs <file>\n");
		System.exit(1);
	}
	
	protected static void readAndAddDimacsSolve(String file, CNFSolver solver) throws Exception {
		DimacsReader r=new DimacsReader();
		r.readSolve(file, solver);
	}
	
	protected static void readAndAddDimacsTrace(String file, ProofTracing solver) throws Exception {
		DimacsReader r=new DimacsReader();
		r.readTrace(file, solver);
	}
}
