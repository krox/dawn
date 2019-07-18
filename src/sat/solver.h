#ifndef SAT_SOLVER_H
#define SAT_SOLVER_H

#include "sat/propengine.h"
#include "sat/solution.h"
#include <cassert>
#include <vector>

/** returns 10=SAT, 20=UNSAT, 30=UNKNWON */
int solve(Sat &sat, Solution &sol);

#endif
