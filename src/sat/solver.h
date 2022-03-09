#pragma once

#include "sat/assignment.h"
#include "sat/propengine.h"
#include <cassert>
#include <vector>

namespace dawn {

/**
 * Solves a SAT problem.
 *   - configured using settings in 'sat.stats' (might be moved at some point)
 *   - returns 10=SAT, 20=UNSAT, 30=UNKNWON (timeout or some other limit)
 */
int solve(Sat &sat, Assignment &sol, SolverConfig const &config);

} // namespace dawn
