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

  public:
	// propEngine has a reference to the activity heap
	Searcher(Searcher const &) = delete;
	Searcher &operator=(Searcher const &) = delete;

	// creating the searcher copies the cnf formula
	Searcher(Sat &sat)
	    : p_(sat, {}), act_(sat.var_count()), polarity_(sat.var_count())
	{
		p_.activity_heap = &act_;
		p_.polarity = &polarity_;
	}

	std::optional<Assignment> run(int nConfls) { return p_.search(nConfls); }
};
} // namespace dawn