#pragma once

#include "sat/sat.h"

#include <climits>

namespace dawn {

struct EliminationConfig
{
	// How much the number of (irreducible) clauses is allowed to grow when
	// eliminating a variable. SatELite/Minisat uses growth=0, cryptominisat
	// uses up to growth=16 I think. growth=infinity completely solve the
	// instance (or, much more likely, run out of memory immediately).
	int growth = 0;

	// When a blocked clause is found, it is marked as reducible. With this
	// option, it is actually removed instead. Note that reducible clauses are
	// never considered anyway, so there is obvious way to remove reducible
	// blocked clauses.
	bool discard_blocked = false;

	// By default, reducible clauses containing eliminated variables are simply
	// discarded. With this option, they are resolved alongside the irreducible
	// clauses.
	//   * Only use with proper limits (e.g. 'max_eliminations'). Otherwise,
	//     this can produce a vast number of additional clauses because
	//     reducible resolvents are not counted towards the 'growth' limit.
	//   * TODO: a compromise where only some reducible resolvents are kept
	bool resolve_reducible = false;

	// maximum number of variables to eliminate
	int64_t max_eliminations = INT64_MAX;

	// maximum number of resolvents to generate before stopping BVE (including
	// reducible resolvents, if 'resolve_reducible' is set)
	int64_t max_resolvents = INT64_MAX;
};

// returns number of removed variables
int run_elimination(Sat &sat, EliminationConfig const &config);

// should this be here?
int run_blocked_clause_addition(Sat &sat);

} // namespace dawn
