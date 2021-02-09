#ifndef SAT_SOLVER_H
#define SAT_SOLVER_H

#include "sat/propengine.h"
#include "sat/solution.h"
#include <cassert>
#include <vector>

/**
 * Solves a SAT problem.
 *   - configured using settings in 'sat.stats' (might be moved at some point)
 *   - returns 10=SAT, 20=UNSAT, 30=UNKNWON (timeout or some other limit)
 */
int solve(Sat &sat, Solution &sol, SolverConfig const &config);

int inprocessCheap(Sat &sat);

#endif
