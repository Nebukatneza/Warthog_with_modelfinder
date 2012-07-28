package de.stzoit.prover.dnnf;

import de.stzoit.prover.cnf.CNFSolver;
import de.stzoit.prover.cnf.Clause;
import de.stzoit.prover.cnf.LearntClause;

import java.util.ArrayList;
import java.util.List;

/**
 * de.stzoit.prover.dnnf.DNNFOperations 
 *
 * (C) 2012 STZOIT, Tuebingen
 *
 * @author Andreas J. Kuebler <andreas.kuebler@stw.de>
 *
 */
public class DNNFOperations extends CNFSolver {
    protected boolean perform_clause_deletion=false;
    protected int assertionLevel = -1;
    protected LearntClause lastLearnt = null;

    public DNNFOperations() {
        super();
    }

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
            //System.out.println(trail);
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

        assertionLevel=(learnt.size()<=1 ? 0 : getLevel(learnt.get(1)));
        lastLearnt=learnt;

        /* add clause, backtrack, propagate uip, restart if threshold is met */
        stats.statConflict();
    }

    /* 
     * citation from "New advances in Compiling CNF to Decomposable Negation 
     * Normal Form":
     *  
     *   decide(l) will set literal l to true and mark the variable of l as a 
     *   decision variable, and assign it a decision level: a number which is 
     *   incremented each time a new decision is made. decide(l) will then 
     *   apply unit resolution which would potentially imply other literals. 
     *   decide(l) succeeds if no contradiction is discovered by unit 
     *   resolution, otherwise, it will fail after having constructed a 
     *   conflict-driven clause as descriped in [zChaff-Paper]. The mentioned
     *   method will construct a conflict-driven clause which is also an 
     *   asserting, in the sense that adding this clause to the knowledge base
     *   will lead to implying the negation of literal l, -l, which is known as
     *   conflict-driven assertion. Another side effect of a failing decide(l) 
     *   is to compute the assertion level, which is the second largest level 
     *   for any literal in the conflict driven clause.
     */
    public boolean decide(int lit) throws Exception {
        newlyImpliedDirty = true;
        level++;
        assign(lit, null);

        if (!bcp()) {
            handleConflict();
            return false;
        }
        return true;
    }

    /* 
     * citation from "New advances in Compiling CNF to Decomposable Negation 
     * Normal Form":
     * 
     *   undo-decide(l) will erase the decision level l and all other literals
     *   that were derived by unit resolution after having asserted l. The 
     *   current decision level will also be decremented.
     */
    public void undoDecide(int var) {
        newlyImpliedDirty = true;
        backtrack(levels.get(var)-1);
    }

    /* 
     * citation from "New advances in Compiling CNF to Decomposable Negation 
     * Normal Form":
     *
     *   at-assertion-level() is a predicate that succeeds if the current 
     *   decision level equals the assertion level computed by the last call to
     *   decide(l).
     */
    public boolean atAssertionLevel() {
        return level == assertionLevel;
    }

    /* 
     * citation from "New advances in Compiling CNF to Decomposable Negation 
     * Normal Form":
     *
     *   assert-cd-literal() will add the conflict-driven clause constructed
     *   by the last call to decide(l). This will in turn lead to implying 
     *   -l, the conflict-driven assertion. Unit resolution will then be 
     *   applied which would potentially imply new literals. This may also 
     *   lead to discovering a contradiction in which case assert-cd-literal() 
     *   will fail, after having constructed a conflict-driven clause and 
     *   computed a new assertion level (just like a call to decide()).
     */
    public boolean assertCdLiteral() throws Exception {
        newlyImpliedDirty = true;
        if (!atAssertionLevel())
            throw new Exception("assertCdLiteral called though not at assertion level!");

        int propLit = lastLearnt.get(0);
        boolean failure = false;

        //System.out.println(lastLearnt);
        failure |= !pushClause(lastLearnt);
        if (lastLearnt.size()>1)
            failure |= !assign(propLit, (lastLearnt.size()==2 ? oppositeLit(lastLearnt.get(1)) : lastLearnt));
        //lastLearnt = null;

        if (failure || !bcp()) {
            handleConflict();
            return false;
        }
        return true;
    }

    private boolean newlyImpliedDirty = true;
    /* 
     * newly implied literals, i.e. all literals on the trail until (but not 
     * including) last decision
     */
    public List<Integer> newlyImplied() {
        List<Integer> rv = new ArrayList<Integer>();
        if (newlyImpliedDirty) {
            int i=trail.size()-1;

            while (i>=0 && (lit2variable(trail.get(i)).reason()!=null || level==0))
                rv.add(trail.get(i--));
        }
        newlyImpliedDirty = false;
        return rv;
    }

    public boolean bcp() {
        newlyImpliedDirty = true;
        return super.bcp();
    }
}
