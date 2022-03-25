#pragma once

#include "sat/sat.h"

#include <climits>

namespace dawn {

struct EliminationConfig
{
	// level 0: remove vars with 0+n occurences (pure / unused variables)
	// level 1: remove vars with 1+1 occurences
	// level 2: remove vars with 1+n occurences
	// level 5: remove vars with <= n+m+growth non-tautology resolvents
	// NOTE: the level "<=1 non-tautology" is not meaningful if we do BCE
	int level = 5;

	// SatELite/Minisat uses growth=0, cryptominisat uses growth=16 I think.
	// growth=infinity can be used to completely solve the instance by
	// resolution (usually not a reasonable thing to do of course)
	int growth = 0;

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

// should this be here?
int run_blocked_clause_addition(Sat &sat);

} // namespace dawn
