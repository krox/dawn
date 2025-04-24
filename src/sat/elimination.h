#pragma once

#include "sat/sat.h"

#include <climits>

namespace dawn {

struct EliminationConfig
{
	// SatELite/Minisat uses growth=0, cryptominisat uses growth=16 I think.
	// growth=infinity can be used to completely solve the instance by
	// resolution (usually not a reasonable thing to do of course)
	int growth = 0;

	int max_eliminations = INT_MAX;
};

// returns number of removed variables
int run_elimination(Sat &sat, EliminationConfig const &config);

// should this be here?
int run_blocked_clause_addition(Sat &sat);

} // namespace dawn
