#pragma once

#include "sat/assignment.h"
#include "sat/propengine.h"
#include <cassert>
#include <stop_token>
#include <vector>

namespace dawn {

/**
 * Solves a SAT problem.
 *   - configured using settings in 'sat.stats' (might be moved at some point)
 *   - returns 10=SAT, 20=UNSAT, 30=UNKNWON (timeout or some other limit)
 */
int solve(Cnf &sat, Assignment &sol, SolverConfig const &config,
          std::stop_token stoken);

} // namespace dawn
