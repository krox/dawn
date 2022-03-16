#pragma once

#include "sat/sat.h"

#include <climits>

namespace dawn {

struct EliminationConfig
{
	// level 0: remove vars with 0+n occurences (pure / unused variables)
	// level 1: remove vars with 1+1 occurences
	// level 2: remove vars with 1+n occurences
	// level 5: remove vars with <= n+m non-tautology resolvents (classical BVE)
	// level 10: remove ALL vars, thus solving the instance by resolution
	// NOTE: the level "<=1 non-tautology" is not meaningful if we do BCE
	int level = 5;

	// if true, only resolve irredcible clauses and simply remove reducible
	// clauses containing a removed variable in the end.
	bool irred_only = true;

	int max_eliminations = INT_MAX;
	bool verbosity = 0; // 0 = summary only, 1 = announce each elimination
};

// returns number of removed variables
int run_elimination(Sat &sat, EliminationConfig const &config);

// returns number of removed clauses
int run_blocked_clause_elimination(Sat &sat);

} // namespace dawn
