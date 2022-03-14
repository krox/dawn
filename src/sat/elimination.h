#pragma once

#include "sat/sat.h"

namespace dawn {

/** returns number of removed variables */
int run_variable_elimination(Sat &sat);

// returns number of removed clauses
int run_blocked_clause_elimination(Sat &sat);

} // namespace dawn
