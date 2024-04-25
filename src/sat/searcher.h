#pragma once

#include "sat/activity_heap.h"
#include "sat/propengine.h"
#include "util/functional.h"

namespace dawn {

// Core of a CDCL solver. This wraps a PropEngine together with some auxiliary
// state (variable activity, polarity).
// TODO: some support to run this concurrently in a separate thread.
//       (depends on copying the CNF formula into the PropEngine or similar)
class Searcher
{
	// number of restarts so far
	int64_t iter_ = 0;

  public:
	PropEngine p_;
	ActivityHeap act_;
	util::bit_vector polarity_;

	struct Config
	{
		// conflict analysis
		int otf = 2; // on-the-fly strengthening of learnt clauses
		             // (0=off, 1=basic, 2=recursive)
		bool full_resolution = false; // learn by full resolution instead of UIP

		// branching heuristic
		int branch_dom = 0; // branch on dominator instead of chosen literal
		                    // (0=off, 1=only matching polarity, 2=always)

		// restarts
		RestartType restart_type = RestartType::luby;
		int restart_base = 100;
		int restart_mult = 1.1; // only for geometric
	};
	Config config;

  public:
	// propEngine has a reference to the activity heap
	Searcher(Searcher const &) = delete;
	Searcher &operator=(Searcher const &) = delete;

	// creating the searcher copies the cnf formula
	Searcher(Sat &sat)
	    : p_(sat), act_(sat.var_count()), polarity_(sat.var_count())
	{}

	// run CDCL for a number of conflicts (or until solution is found)
	//   - maxConflicts can be slightly exceeded in case a learnt clause
	//     immediately leads to another conflict
	//   - returns solution if found, nullopt if limits reached or
	//     contradiction is found
	//   - behaviour is controlled by config (see above)
	//   - learnt clauses are automatically added to the Searcher itself. To get
	//     them back into the original Sat/Cnf instance, use the callback.
	std::optional<Assignment>
	run(util::function_view<void(std::span<const Lit>)> on_learnt);
};
} // namespace dawn