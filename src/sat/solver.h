#ifndef SAT_SOLVER_H
#define SAT_SOLVER_H

#include "sat/propengine.h"
#include "sat/solution.h"
#include <cassert>
#include <vector>

/** returns empty if contradiction is found */
bool solve(Sat &sat, Solution &sol);

#endif
