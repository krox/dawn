#ifndef SOLVER_H
#define SOLVER_H

#include <vector>
#include <cassert>
#include "propengine.h"

/** returns empty if contradiction is found */
std::vector<bool> solve(ClauseSet& cs);

#endif
