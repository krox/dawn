#pragma once

#include "sat/activity_heap.h"
#include "sat/propengine.h"

namespace dawn {

// Core of a CDCL solver. This wraps a PropEngine together with some auxiliary
// state (variable activity, polarity).
// TODO: some support to run this concurrently in a separate thread.
//       (depends on copying the CNF formula into the PropEngine or similar)
class Searcher
{
  public:
	PropEngine p_;
	ActivityHeap act_;
	util::bit_vector polarity_;

	struct Config
	{
		int otf = 2; // on-the-fly strengthening of learnt clauses
		             // (0=off, 1=basic, 2=recursive)
		bool full_resolution = false; // learn by full resolution instead of UIP
		int branch_dom = 0; // branch on dominator instead of chosen literal
		                    // (0=off, 1=only matching polarity, 2=always)s
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

	// run CDCL for up to maxConfl conflicts (or until solution is found)
	//   - does not perform restarts, such searches on from whatever the current
	//     state (i.e. partial assignment) is.
	//   - maxConflicts can be slightly exceeded in case a learnt clause
	//     immediately leads to another conflict
	//   - returns solution if found, nullopt if limits reached or
	//     contradiction is found
	//   - behaviour is controlled by config (see above)
	std::optional<Assignment> run(int nConfls);
};
} // namespace dawn