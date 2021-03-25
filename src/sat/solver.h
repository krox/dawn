#pragma once

#include "sat/propengine.h"
#include "sat/solution.h"
#include <cassert>
#include <vector>

namespace dawn {

/**
 * Solves a SAT problem.
 *   - configured using settings in 'sat.stats' (might be moved at some point)
 *   - returns 10=SAT, 20=UNSAT, 30=UNKNWON (timeout or some other limit)
 */
int solve(Sat &sat, Solution &sol, SolverConfig const &config);

} // namespace dawn
