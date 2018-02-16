#ifndef SOLVER_H
#define SOLVER_H

#include <vector>
#include <cassert>
#include "propengine.h"
#include "solution.h"

/** returns empty if contradiction is found */
bool solve(ClauseSet& cs, Solution& sol);

#endif
