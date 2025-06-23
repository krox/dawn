#pragma once

#include "sat/cnf.h"

#include <climits>

namespace dawn {

struct EliminationConfig
{
	// How much the number of (irreducible) clauses is allowed to grow when
	// eliminating a variable. SatELite/Minisat uses growth=0, cryptominisat
	// uses up to growth=16 I think. growth=infinity completely solves the
	// instance (or, much more likely, runs out of memory quickly).
	int growth = 0;

	// When a blocked clause is found, it is marked as reducible. With this
	// option, it is actually removed instead. Note that reducible clauses are
	// never considered anyway, so there is obvious way to remove reducible
	// blocked clauses.
	bool discard_blocked = false;

	// Maximum size of reducible resolvents.
	//   * Classic SatELite/Minisat just discards all reducible resolvents when
	//     eliminating a variable. We instead resolve them along with the
	//     irreducible ones, but only keep them if they are particularly short.
	//   * Make sure to set proper limits (e.g. 'max_eliminations') if you want
	//     to be generous with these. Otherwise, this can produce a vast number
	//     of additional clauses because reducible resolvents are not counted
	//     towards the 'growth' limit.
	//   * TODO: increase the default a bit if/when we get better
	//     otf-subsumption. Should probably be in line with the 'green cutoff'
	//     in the CDCL searcher.
	int green_cutoff = 3;

	// maximum number of variables to eliminate
	int64_t max_eliminations = INT64_MAX;

	// maximum number of resolvents to generate before stopping
	//   * reducible resolvents are counted towards this limit (assuming they
	//     pass the '.green_cutoff' limit)
	int64_t max_resolvents = 20'000;
};

// returns number of removed variables
int run_elimination(Cnf &, EliminationConfig const &config);

// should this be here?
int run_blocked_clause_addition(Cnf &);

} // namespace dawn
