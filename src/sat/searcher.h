#pragma once

#include "sat/activity_heap.h"
#include "sat/propengine.h"
#include "util/functional.h"
#include <stop_token>

namespace dawn {

// Core of a CDCL solver. This wraps a PropEngine together with some auxiliary
// state (variable activity, polarity).
//   * 'Searcher' owns all its data (clauses, activity heap, ...), so multiple
//     instances can be created and run concurrently. Resulting learnt clauses
//     are communicated back to the caller via a callback.
// TODO: some support to run this concurrently in a separate thread.
//       (depends on copying the CNF formula into the PropEngine or similar)
class Searcher
{
	// number of restarts so far
	int64_t iter_ = 0;

	// temporary buffer for learnt clauses
	std::vector<Lit> buf_;

	PropEngine p_;
	ActivityHeap act_;
	util::bit_vector polarity_;

	// analyze + otf-shorten + backtrack + propagate + callback
	void
	handle_conflict(util::function_view<Color(std::span<const Lit>)> on_learnt);

	// run one 'restart', i.e. starting and ending at decision level 0
	//   * number of conflicts in this restart is determined by config
	std::optional<Assignment>
	run_restart(util::function_view<Color(std::span<const Lit>)> on_learnt,
	            std::stop_token stoken);

  public:
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
		float restart_mult = 1.1; // only for geometric

		// mic
		int green_cutoff = 8; // max size of clause to be considered good
	};
	Config config;

	// Not moveable
	// (internal note: the PropEngine contains a reference to the activity heap)
	Searcher(Searcher const &) = delete;
	Searcher &operator=(Searcher const &) = delete;

	PropStats const &stats() const { return p_.stats; }

	// This copies all clauses into the Searcher, so that it can be used
	// indepndent of the original CNF formula.
	Searcher(Cnf const &cnf)
	    : p_(cnf), act_(cnf.var_count()), polarity_(cnf.var_count())
	{}

	// Keeps running restarts until a satisfying assignment or a contradiction
	// is found, or some limit is reached.
	//   * Returned ClauseStorage contains all 'good' learnt clauses of this
	//     epoch (as determined by .config.green_cutoff). Clause-cleaning
	//     policies inside the Searcher are in principle independent of what the
	//     caller considers a 'good' clause. (Typically, the searcher will
	//     retain more clauses internally, at least for a while.)
	//   * If a contradiction is found, a ClauseStorage containing an empty
	//     clause will be returned.
	//   * 'max_confls' can be exceeded by a small margin, as the search will
	//     stop at the next restart.
	//   * This function is not thread-safe. Use multiple instances of
	//     'Searcher' in order to parallelize.
	std::variant<ClauseStorage, Assignment> run_epoch(int64_t max_confls,
	                                                  std::stop_token stoken);
};
} // namespace dawn